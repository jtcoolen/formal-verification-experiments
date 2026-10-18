#!/usr/bin/env bash
# noLeftRecursion: iterP left-corner closure vs memoized closure.
set -u
cd "$(dirname "$0")" || exit 1
LIMIT=60
OUT=bench7-results; mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
run_one () {
  name="$1"; body="$2"
  { echo 'import Bench.MemoLC'; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp7_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp7_$name.lean" >"$OUT/$name.log" 2>"$OUT/$name.time"
  read -r el rc < "$OUT/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-24s %10s\n' "$name" "$tot" | tee -a "$OUT/summary.txt"
}
lake build Bench.MemoLC > /dev/null 2>&1 || { echo 'Bench.MemoLC failed'; exit 1; }
for k in 4 8 16; do
  run_one "lc${k}_iterp" "(Bench.circ $k).noLeftRecursion = true"
  run_one "lc${k}_memo"  "(Bench.MemoLC.nlrMemo (Bench.circ $k)) = true"
done
