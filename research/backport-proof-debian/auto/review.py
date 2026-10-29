"""Have a second agent read the stated properties (PROTOCOL-auto.md §3.9).

The case notes up to their 「結果」 section (so without whether the proof went through)
are given to a fresh `claude -p` with read-only tools, together with the advisory,
Debian's patch and the upstream fix. It answers four fixed questions in a JSON schema.
The answer is recorded and published next to the verdict; it never changes the verdict,
because the reader is an AI as well.

Usage (prove.py calls review()):
    python3 review.py <case-notes.md> <input-dir> <manifest.json> [--claude CMD]
"""
import json
import shlex
import string
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROMPT = HERE / 'review-prompt.md'
RESULTS_HEADING = '## 結果'
QUESTIONS = ('p1_states_fix', 'p0_states_bug', 'scope_keeps_the_path', 'specs_keep_the_behavior')
TIMEOUT = 1800
ANSWER = {'type': 'object', 'properties': {'ok': {'type': 'boolean'}, 'reason': {'type': 'string'}},
          'required': ['ok', 'reason']}
SCHEMA = {'type': 'object',
          'properties': {**{q: ANSWER for q in QUESTIONS}, 'summary': {'type': 'string'}},
          'required': [*QUESTIONS, 'summary']}
CLAUDE = ['claude', '-p', '--output-format', 'json', '--allowedTools', 'Read Glob Grep WebFetch',
          '--disallowedTools', 'Bash Edit Write', '--json-schema', json.dumps(SCHEMA)]


def statement(notes: str) -> str:
    """The notes before the results section; the reader must not see the outcome."""
    cut = notes.find('\n' + RESULTS_HEADING)
    return notes if cut < 0 else notes[:cut + 1]


def render(manifest: dict, statement_path: Path, input_dir: Path) -> str:
    values = {k: v for k, v in manifest.items() if isinstance(v, str)}
    return string.Template(PROMPT.read_text()).substitute(
        {**values, 'statement': str(statement_path), 'input_dir': str(input_dir)})


def parse(stdout: str) -> dict | None:
    """The structured answer from `claude -p --output-format json`, or None."""
    try:
        doc = json.loads(stdout)
    except json.JSONDecodeError:
        return None
    answer = doc.get('structured_output') if isinstance(doc, dict) else None
    if answer is None and isinstance(doc, dict) and isinstance(doc.get('result'), str):
        try:
            answer = json.loads(doc['result'])
        except json.JSONDecodeError:
            return None
    return answer if valid(answer) else None


def valid(answer: object) -> bool:
    if not isinstance(answer, dict) or not isinstance(answer.get('summary'), str):
        return False
    return all(isinstance(answer.get(q), dict) and isinstance(answer[q].get('ok'), bool)
               and isinstance(answer[q].get('reason'), str) for q in QUESTIONS)


def summarize(answer: dict | None, error: str = '') -> dict:
    """What prove.json and VERDICTS.md carry."""
    if answer is None:
        return {'status': '読み直しできず', 'problems': [], 'summary': '', 'error': error[-500:]}
    problems = [q for q in QUESTIONS if not answer[q]['ok']]
    return {'status': '指摘あり' if problems else '指摘なし', 'problems': problems,
            'summary': answer['summary'], 'answers': answer}


def review(notes: Path, input_dir: Path, manifest: dict, cmd: list[str] = CLAUDE,
           cwd: Path | None = None) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        stmt = Path(tmp) / notes.name
        stmt.write_text(statement(notes.read_text()))
        prompt = render(manifest, stmt, input_dir)
        try:
            proc = subprocess.run([*cmd, '--add-dir', tmp, '--add-dir', str(input_dir)] if cmd is CLAUDE else cmd,
                                  input=prompt,
                                  capture_output=True, text=True, timeout=TIMEOUT, cwd=cwd)
        except subprocess.TimeoutExpired:
            return summarize(None, f'timed out after {TIMEOUT}s')
    answer = parse(proc.stdout)
    return summarize(answer, '' if answer else f'exit {proc.returncode}: {proc.stdout[-300:]} {proc.stderr[-200:]}')


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    cmd = shlex.split(argv[argv.index('--claude') + 1]) if '--claude' in argv else CLAUDE
    out = review(Path(argv[0]), Path(argv[1]).resolve(), json.loads(Path(argv[2]).read_text()), cmd)
    print(json.dumps(out, ensure_ascii=False, indent=1))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
