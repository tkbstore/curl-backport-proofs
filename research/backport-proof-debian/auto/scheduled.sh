#!/bin/sh
# PROTOCOL-auto.md §5 の定期実行。CI は使わない。
#   scheduled.sh install <公開リポジトリの clone>   launchd に毎日 03:00 の実行を登録する
#   scheduled.sh                                   1回まわす（launchd から呼ばれる）
# このスクリプトがある checkout（パイプライン専用の clone、auto/pipeline）で run.py を動かす。置き場所は ~/Documents の外（PROTOCOL-auto §5）。
#   CBP_PUBLIC      公開リポジトリの clone（必須。install が plist に書く）
#   CBP_WORK        作業ディレクトリ（既定 ~/.local/share/curl-backport-proofs）
#   CBP_MAX_PROOFS  1回で証明する件数の上限（既定 1）
set -u
here=$(cd "$(dirname "$0")" && pwd)
label=jp.tkbase.curl-backport-proofs
work="${CBP_WORK:-$HOME/.local/share/curl-backport-proofs}"

if [ "${1:-}" = install ]; then
  public=$(cd "${2:?usage: scheduled.sh install <public-clone>}" && pwd)
  plist="$HOME/Library/LaunchAgents/$label.plist"
  mkdir -p "$work" "$(dirname "$plist")"
  cat > "$plist" <<EOF
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
  <key>Label</key><string>$label</string>
  <key>ProgramArguments</key><array><string>/bin/sh</string><string>$here/scheduled.sh</string></array>
  <key>EnvironmentVariables</key><dict>
    <key>CBP_PUBLIC</key><string>$public</string>
    <key>CBP_WORK</key><string>$work</string>
    <key>PATH</key><string>$PATH</string>
  </dict>
  <key>StartCalendarInterval</key><dict><key>Hour</key><integer>3</integer><key>Minute</key><integer>0</integer></dict>
  <key>StandardErrorPath</key><string>$work/launchd.err</string>
</dict>
</plist>
EOF
  plutil -lint "$plist" || exit 1
  launchctl unload "$plist" 2>/dev/null
  launchctl load "$plist" && echo "loaded $plist"
  exit $?
fi

public="${CBP_PUBLIC:?CBP_PUBLIC (the public clone) is required}"
mkdir -p "$work/logs"
log="$work/logs/$(date '+%Y-%m-%dT%H%M%S').log"
{
  date '+start %F %T'
  git -C "$public" pull -q --ff-only origin main
  # コードの更新は GitHub の auto/pipeline から受け取る（~/Documents は launchd から読めない: TCC）
  # ローカルの auto/pipeline には証明のマージが積まれていて origin と枝分かれする。--no-rebase が無いと git は pull を拒む
  git -C "$here" pull -q --no-rebase --no-edit origin auto/pipeline || echo "pull of auto/pipeline failed; running the checked-out code"
  # 実行中はスリープさせない。眠ると API の接続が切れて証明のジョブが落ちる（2026-10-31 の CVE-2023-27533）。
  # -i はアイドルによるスリープ、-s は電源につないでいる間のシステムのスリープを止める。蓋を閉じた電池駆動は止められない
  caffeinate -i -s python3 "$here/run.py" --public "$public" --work "$work" --max-proofs "${CBP_MAX_PROOFS:-1}"
  echo "exit $?"
  date '+end %F %T'
} >> "$log" 2>&1
