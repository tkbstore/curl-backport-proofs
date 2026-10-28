#!/bin/sh
# PROTOCOL §5 の上限（1件あたり lake build 80 回）を数えるためのラッパー。
# 使い方: ./build.sh <case>   例: ./build.sh case5
# 1回呼ぶごとに build-log.tsv に「時刻・件・終了コード」を1行足す。
set -u
case_id="${1:?case id required}"
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
# BUILD_LIMIT が設定されていれば、その件の回数が上限に達したところで lake build を走らせない（auto/prove.py が設定する）。
if [ -n "${BUILD_LIMIT:-}" ]; then
  done_n=$(grep -c "	$case_id	" build-log.tsv 2>/dev/null)
  if [ "${done_n:-0}" -ge "$BUILD_LIMIT" ]; then
    echo "limit reached: count[$case_id]=$done_n >= BUILD_LIMIT=$BUILD_LIMIT (lake build not run)"
    exit 3
  fi
fi
out=$(lake build 2>&1); code=$?
printf '%s\t%s\t%s\n' "$(date '+%F %T')" "$case_id" "$code" >> build-log.tsv
printf '%s\n' "$out" | awk '/^(error|warning): [A-Za-z0-9_]+\.lean:/{p=1} /^(✔|⣿|trace|info)/{p=0} /Build completed|^error: build failed/{print; next} p' | grep -v "^warning" | head -${BUILD_LINES:-80}
echo "count[$case_id]=$(grep -c "	$case_id	" build-log.tsv)"
