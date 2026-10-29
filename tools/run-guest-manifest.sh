#!/usr/bin/env bash
# run-guest-manifest.sh MANIFEST [JOBS] [SECONDS]
# Run every input of an EEST manifest (as written by tools/make-inputs.sh:
# name, input path, expected output hex) through `lake exe run-guest`, the
# executable source model with the challenge's ordinary-memory domain, and
# compare the guest's output region with the expected bytes. Prints one
# OK/MISMATCH/TIMEOUT line per input and exits non-zero unless all are OK.
# The model is an interpreter: heavy blocks can take far longer than on a
# machine, so SECONDS (default 14400) bounds each run; the heaviest
# sample blocks take about 70 minutes.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
manifest="${1:?usage: run-guest-manifest.sh MANIFEST [JOBS] [SECONDS]}"
jobs="${2:-8}"
seconds="${3:-14400}"
cd "$ROOT"
lake build run-guest >/dev/null
export RUN_GUEST="$ROOT/.lake/build/bin/run-guest" SECONDS_LIMIT="$seconds"
results=$(mktemp)
trap 'rm -f "$results"' EXIT
cut -f1-3 "$manifest" | xargs -P "$jobs" -L 1 bash -c '
  name=$0 input=$1 expected=$2 status=0
  out=$(timeout "$SECONDS_LIMIT" "$RUN_GUEST" "$input" 2>&1) || status=$?
  if [[ $status == 124 ]]; then echo "TIMEOUT $name"; exit 0; fi
  if [[ $status != 0 ]]; then echo "MISMATCH $name: exit $status"; exit 0; fi
  result=$(sed -n 2p <<<"$out")
  got=$(sed -n "s/^output\[0..80): //p" <<<"$out")
  if [[ ${got:0:${#expected}} == "$expected" ]]; then
    echo "OK $name: $result"
  else
    echo "MISMATCH $name: $result"
  fi' | tee "$results"
total=$(wc -l < "$results")
ok=$(grep -c "^OK" "$results" || true)
echo "$ok/$total OK"
[[ $ok == "$total" ]]
