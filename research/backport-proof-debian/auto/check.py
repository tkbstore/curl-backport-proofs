"""Run the mechanical checks of PROTOCOL-auto.md §4 on case records (§3.7).

For each cases/<patch>.json given on the command line:
  - `lake build` of the whole tree succeeds (run once for all cases, via lean/build.sh)
  - every main theorem's `#print axioms` is a subset of ALLOWED_AXIOMS
  - no `sorry` / `admit` / `native_decide` / `bv_decide` / `axiom` declaration in the
    files of `lean_modules` and the Deb* / GenDeb* files they import (comments and
    strings are skipped)
  - the D1 / D0 theorems mention the Clight functions in `d_functions`: the name appears
    in the `#check` output, or among the constants of the theorem's type after unfolding
    reducible definitions (`abbrev FD1 := …_d1.f_…`)
  - a record with `p0_on_fixed` 「成立」 names the theorems in `theorems.P0_on_fixed`
    (P0 restated on the fixed function, §3.10); they get the same axiom and source checks

A case whose verdict is not 「同じ性質」 may have no theorems; it is reported as
「確認する定理が無い」. Prints one JSON document to stdout. Exit code 0 when no case
failed, 1 otherwise, 2 on bad usage. Nothing here needs a human decision.

The probe file lean/ProbeAutoCheck.lean (gitignored as lean/Probe*.lean) is overwritten
on every run and left in place; do not run two checks on the same tree at once.
`lake build` goes through lean/build.sh, which appends one line to build-log.tsv.

Usage:
    python3 check.py <case.json>... [--no-build] [--lean-dir DIR]
    e.g. python3 check.py ../cases/*.json
"""
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_LEAN_DIR = HERE.parents[1] / 'c-semantics-link' / 'lean'
BUILD_CASE_ID = 'auto-check'
PROBE_NAME = 'ProbeAutoCheck.lean'
LEAN_TIMEOUT = 1800
BUILD_TIMEOUT = 7200

SAME = '同じ性質'
VERDICTS = (SAME, '証明できず', '上流と仕組みが違う', '対象外（大きさ）',
            '上流の修正を特定できない', 'パッチが当たらない')
SLOTS = ('U1', 'U0', 'D1', 'D0')
D_SLOTS = ('D1', 'D0')
CROSS_SLOT = 'P0_on_fixed'
THEOREM_KEYS = SLOTS + (CROSS_SLOT,)
CROSS_HOLDS = '成立'
CROSS_RESULTS = (CROSS_HOLDS, '示せず')
ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound',
                            'CC.externalFunctionsSem', 'CC.inlineAssemblySem'})
FORBIDDEN_WORDS = re.compile(r'(?<![\w.\'])(sorry|admit|native_decide|bv_decide)(?![\w\'])')
AXIOM_DECL = re.compile(
    r'^[ \t]*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*axiom\b',
    re.MULTILINE)
SCANNED_MODULE = re.compile(r'^(Gen)?Deb')
IMPORT_LINE = re.compile(r'^\s*import\s+(.+)$', re.MULTILINE)
NAME = re.compile(r'^[A-Za-z_][\w\']*(\.[A-Za-z_][\w\']*)*$')
DEPENDS = re.compile(r"depends on axioms:\s*\[(.*?)\]", re.DOTALL)
NO_AXIOMS = 'does not depend on any axioms'

RESULT_PASS = '合格'
RESULT_FAIL = '不合格'
RESULT_NO_THEOREMS = '確認する定理が無い'

# Prints the constants of a theorem's type, unfolding reducible definitions (abbrev).
USES_DEF = """open Lean in
def autoCheckUses (thm : Name) : CoreM Unit := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := (← getConstInfo thm).type.getUsedConstants.toList
  let mut fuel := 20000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      if (← getReducibilityStatus n) == .reducible then
        if let some (.defnInfo d) := env.find? n then
          todo := d.value.getUsedConstants.toList ++ todo
  IO.println (" ".intercalate (seen.toList.map toString))
"""


@dataclass(frozen=True)
class Case:
    path: str
    patch: str
    verdict: str
    lean_modules: tuple[str, ...]
    theorems: dict[str, tuple[str, ...]]
    d_functions: dict[str, tuple[str, ...]]
    p0_on_fixed: str | None = None


@dataclass
class CaseResult:
    case: str
    patch: str
    verdict: str
    result: str = RESULT_PASS
    reasons: list[str] = field(default_factory=list)
    axioms: dict[str, list[str]] = field(default_factory=dict)
    d_found: dict[str, str] = field(default_factory=dict)
    scanned_files: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class ProbeOutput:
    axioms: dict[str, list[str] | None]  # None: no `#print axioms` answer
    checks: dict[str, str | None]        # None: `#check` failed
    uses: dict[str, list[str] | None]    # constants of the type, through reducible defs
    errors: tuple[str, ...]


# ---------------------------------------------------------------- loading

def _names(value: object, where: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(x, str) and NAME.match(x) for x in value):
        raise ValueError(f'{where}: a list of Lean names is required')
    return tuple(value)


def _slot_map(value: object, slots: tuple[str, ...], where: str) -> dict[str, tuple[str, ...]]:
    if not isinstance(value, dict):
        raise ValueError(f'{where}: an object is required')
    unknown = set(value) - set(slots)
    if unknown:
        raise ValueError(f'{where}: unknown keys {sorted(unknown)}')
    return {k: _names(value[k], f'{where}.{k}') for k in slots if k in value}


def load_case(path: Path) -> Case:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise ValueError('the record must be a JSON object')
    for key in ('patch', 'verdict'):
        if not isinstance(data.get(key), str):
            raise ValueError(f'{key}: a string is required')
    if data['verdict'] not in VERDICTS:
        raise ValueError(f'verdict: {data["verdict"]!r} is not one of §3.6')
    cross = data.get('p0_on_fixed')
    if cross is not None and cross not in CROSS_RESULTS:
        raise ValueError(f'p0_on_fixed: {cross!r} is not one of {CROSS_RESULTS}')
    return Case(
        path=str(path), patch=data['patch'], verdict=data['verdict'],
        lean_modules=_names(data.get('lean_modules', []), 'lean_modules'),
        theorems=_slot_map(data.get('theorems', {}), THEOREM_KEYS, 'theorems'),
        d_functions=_slot_map(data.get('d_functions', {}), D_SLOTS, 'd_functions'),
        p0_on_fixed=cross)


def all_theorems(case: Case) -> list[str]:
    return [t for slot in THEOREM_KEYS for t in case.theorems.get(slot, ())]


def d_theorems(case: Case) -> list[str]:
    return [t for slot in D_SLOTS for t in case.theorems.get(slot, ())]


# ---------------------------------------------------------------- lean

def lean_env() -> dict[str, str]:
    env = dict(os.environ)
    env['PATH'] = f'{Path.home() / ".elan" / "bin"}:{env.get("PATH", "")}'
    return env


def run_build(lean_dir: Path) -> tuple[bool, str]:
    """Run build.sh once; its exit code is the last `auto-check` line of build-log.tsv."""
    proc = subprocess.run(['./build.sh', BUILD_CASE_ID], cwd=lean_dir, env={**lean_env(), 'BUILD_LINES': '40'},
                          capture_output=True, text=True, timeout=BUILD_TIMEOUT)
    log = lean_dir / 'build-log.tsv'
    rows = [r.split('\t') for r in log.read_text().splitlines() if r.count('\t') >= 2] if log.exists() else []
    codes = [r[2] for r in rows if r[1] == BUILD_CASE_ID]
    if proc.returncode != 0 or not codes:
        return False, f'build.sh did not run (exit {proc.returncode}): {proc.stderr.strip()[:500]}'
    tail = '\n'.join(proc.stdout.strip().splitlines()[-15:])
    return codes[-1] == '0', f'lake build exit {codes[-1]}\n{tail}'


def probe_source(modules: list[str], theorems: list[str],
                 with_uses: set[str]) -> tuple[str, dict[int, tuple[str, str]]]:
    """Lean source and a map from line number (1-based) to (command, theorem)."""
    lines = ['import Lean'] + [f'import {m}' for m in modules]
    lines += ['set_option format.width 1000000', 'set_option pp.fullNames true']
    lines += USES_DEF.splitlines()
    where: dict[int, tuple[str, str]] = {}
    for thm in theorems:
        lines.append(f'#print axioms {thm}')
        where[len(lines)] = ('axioms', thm)
        lines.append(f'#check @{thm}')
        where[len(lines)] = ('check', thm)
        if thm in with_uses:
            lines.append(f'#eval autoCheckUses `{thm}')
            where[len(lines)] = ('uses', thm)
    return '\n'.join(lines) + '\n', where


def parse_axioms(text: str) -> list[str] | None:
    if NO_AXIOMS in text:
        return []
    match = DEPENDS.search(text)
    if not match:
        return None
    return [a.strip() for a in match.group(1).replace('\n', ' ').split(',') if a.strip()]


def run_probe(lean_dir: Path, modules: list[str], theorems: list[str], with_uses: set[str]) -> ProbeOutput:
    source, where = probe_source(modules, theorems, with_uses)
    (lean_dir / PROBE_NAME).write_text(source)
    proc = subprocess.run(['lake', 'env', 'lean', '--json', PROBE_NAME], cwd=lean_dir, env=lean_env(),
                          capture_output=True, text=True, timeout=LEAN_TIMEOUT)
    axioms: dict[str, list[str] | None] = {t: None for t in theorems}
    checks: dict[str, str | None] = {t: None for t in theorems}
    uses: dict[str, list[str] | None] = {t: None for t in with_uses}
    errors: list[str] = []
    for raw in proc.stdout.splitlines():
        try:
            msg = json.loads(raw)
        except json.JSONDecodeError:
            errors.append(raw)
            continue
        line = msg.get('pos', {}).get('line', 0)
        text = msg.get('data', '')
        kind, thm = where.get(line, ('', ''))
        if msg.get('severity') == 'error':
            errors.append(f'line {line}: {text}')
        elif kind == 'axioms':
            axioms[thm] = parse_axioms(text)
        elif kind == 'check':
            checks[thm] = text
        elif kind == 'uses':
            uses[thm] = text.split()
    if proc.stderr.strip():
        errors.append(proc.stderr.strip()[:2000])
    return ProbeOutput(axioms, checks, uses, tuple(errors))


# ---------------------------------------------------------------- source scan

def strip_comments_and_strings(src: str) -> str:
    """Replace Lean comments (nested `/- -/`, `--`) and string literals with spaces."""
    out: list[str] = []
    i, depth, n = 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if depth:
            if two == '/-':
                depth, i = depth + 1, i + 2
            elif two == '-/':
                depth, i = depth - 1, i + 2
            else:
                out.append('\n' if src[i] == '\n' else ' ')
                i += 1
        elif two == '/-':
            depth, i = 1, i + 2
        elif two == '--':
            end = src.find('\n', i)
            i = n if end < 0 else end
        elif src[i:i + 3] == "'\"'":
            out.append('   ')
            i += 3
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            out.append(' ' * (j + 1 - i))
            i = j + 1
        else:
            out.append(src[i])
            i += 1
    return ''.join(out)


def module_file(lean_dir: Path, module: str) -> Path:
    return lean_dir / (module.replace('.', '/') + '.lean')


def import_closure(lean_dir: Path, roots: tuple[str, ...]) -> tuple[list[str], list[str]]:
    """Local modules reachable from roots, and roots that have no file."""
    seen: list[str] = []
    missing = [m for m in roots if not module_file(lean_dir, m).exists()]
    todo = [m for m in roots if m not in missing]
    while todo:
        mod = todo.pop()
        if mod in seen:
            continue
        seen.append(mod)
        text = strip_comments_and_strings(module_file(lean_dir, mod).read_text())
        for group in IMPORT_LINE.findall(text):
            todo += [m for m in group.split() if module_file(lean_dir, m).exists() and m not in seen]
    return sorted(seen), missing


def forbidden_in(path: Path) -> list[str]:
    code = strip_comments_and_strings(path.read_text())
    hits = [f'{path.name}:{code.count(chr(10), 0, m.start()) + 1}: {m.group(1)}'
            for m in FORBIDDEN_WORDS.finditer(code)]
    hits += [f'{path.name}:{code.count(chr(10), 0, m.start()) + 1}: axiom の宣言'
             for m in AXIOM_DECL.finditer(code)]
    return hits


# ---------------------------------------------------------------- judging

def check_axioms(case: Case, probe: ProbeOutput, res: CaseResult) -> None:
    for thm in all_theorems(case):
        axioms = probe.axioms.get(thm)
        if axioms is None:
            res.reasons.append(f'{thm}: #print axioms の結果が無い（名前が無いか、読み込みに失敗）')
            continue
        res.axioms[thm] = axioms
        extra = sorted(set(axioms) - ALLOWED_AXIOMS)
        if extra:
            res.reasons.append(f'{thm}: 許していない公理 {extra}')


def check_d_functions(case: Case, probe: ProbeOutput, res: CaseResult) -> None:
    for slot in D_SLOTS:
        slot_thms = case.theorems.get(slot, ())
        text = '\n'.join(probe.checks.get(t) or '' for t in slot_thms)
        used = {u for t in slot_thms for u in (probe.uses.get(t) or [])}
        for fn in case.d_functions.get(slot, ()):
            if re.search(rf'(?<![\w.]){re.escape(fn)}(?![\w\'])', text):
                res.d_found[f'{slot}:{fn}'] = '#check'
            elif fn in used:
                res.d_found[f'{slot}:{fn}'] = '型の定数（reducible な定義を展開）'
            else:
                res.reasons.append(f'{slot}: D の定理（{", ".join(slot_thms) or "無し"}）が {fn} を指していない')


def check_sources(case: Case, lean_dir: Path, res: CaseResult) -> None:
    files, missing = import_closure(lean_dir, case.lean_modules)
    res.reasons.extend(f'lean_modules の {mod} のファイルが無い' for mod in missing)
    res.scanned_files = [m for m in files if m in case.lean_modules or SCANNED_MODULE.match(m.split('.')[-1])]
    for mod in res.scanned_files:
        res.reasons.extend(f'禁止した語: {hit}' for hit in forbidden_in(module_file(lean_dir, mod)))


def judge(case: Case, built: bool, probe: ProbeOutput, lean_dir: Path) -> CaseResult:
    res = CaseResult(case=case.path, patch=case.patch, verdict=case.verdict)
    if case.verdict != SAME and not all_theorems(case):
        res.result = RESULT_NO_THEOREMS
        res.reasons.append(f'判定が「{case.verdict}」で、theorems が空')
        return res
    if not built:
        res.reasons.append('lake build が成功していない')
    if case.verdict == SAME:
        res.reasons.extend(f'theorems.{s} が空（判定「同じ性質」には4つとも要る）'
                           for s in SLOTS if not case.theorems.get(s))
        res.reasons.extend(f'd_functions.{s} が空' for s in D_SLOTS if not case.d_functions.get(s))
    if not case.lean_modules:
        res.reasons.append('lean_modules が空')
    if case.p0_on_fixed == CROSS_HOLDS and not case.theorems.get(CROSS_SLOT):
        res.reasons.append(f'p0_on_fixed が「{CROSS_HOLDS}」で、theorems.{CROSS_SLOT} が空')
    check_axioms(case, probe, res)
    check_d_functions(case, probe, res)
    check_sources(case, lean_dir, res)
    if res.reasons:
        res.result = RESULT_FAIL
    return res


def parse_args(argv: list[str]) -> tuple[list[str], bool, Path]:
    args = [a for a in argv if a != '--no-build']
    lean_dir = DEFAULT_LEAN_DIR
    if '--lean-dir' in args:
        i = args.index('--lean-dir')
        if i + 1 >= len(args):
            raise ValueError('--lean-dir needs a directory')
        lean_dir, args = Path(args[i + 1]).resolve(), args[:i] + args[i + 2:]
    return args, '--no-build' not in argv, lean_dir


def main(argv: list[str]) -> int:
    try:
        paths, build, lean_dir = parse_args(argv)
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 2
    if not paths:
        print(__doc__, file=sys.stderr)
        return 2
    cases: list[Case] = []
    broken: list[CaseResult] = []
    for arg in paths:
        try:
            cases.append(load_case(Path(arg)))
        except (OSError, ValueError) as exc:
            broken.append(CaseResult(case=arg, patch='', verdict='', result=RESULT_FAIL,
                                     reasons=[f'記録を読めない: {exc}']))
    built, build_detail = run_build(lean_dir) if build else (True, 'skipped (--no-build)')
    modules = sorted({m for c in cases if all_theorems(c) for m in c.lean_modules
                      if module_file(lean_dir, m).exists()})
    theorems = sorted({t for c in cases for t in all_theorems(c)})
    with_uses = {t for c in cases for t in d_theorems(c)}
    probe = run_probe(lean_dir, modules, theorems, with_uses) if theorems else ProbeOutput({}, {}, {}, ())
    results = broken + [judge(c, built, probe, lean_dir) for c in cases]
    report = {
        'build': {'ok': built, 'detail': build_detail},
        'probe_errors': list(probe.errors),
        'summary': {r: sum(1 for x in results if x.result == r)
                    for r in (RESULT_PASS, RESULT_FAIL, RESULT_NO_THEOREMS)},
        'cases': [asdict(r) for r in results],
    }
    print(json.dumps(report, ensure_ascii=False, indent=1))
    return 1 if any(r.result == RESULT_FAIL for r in results) else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
