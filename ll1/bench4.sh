#!/usr/bin/env bash
# Large-size comparison for the scaled circuit family: k = 12, 16.
set -u
cd "$(dirname "$0")" || exit 1
LIMIT=60
IMP=Bench.Circ
OUT=bench3-results-large; mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
run_one () {
  name="$1"; body="$2"
  { echo "import $IMP"; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp4_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp4_$name.lean" >"$OUT/$name.log" 2>"$OUT/$name.time"
  read -r el rc < "$OUT/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-22s %10s\n' "$name" "$tot" | tee -a "$OUT/summary.txt"
}
for k in 12 16; do
  run_one "ref_ll1check_$k" "(Bench.circ $k).ll1Check = true"
  run_one "fol_ll1check_$k" "(Bench.Memo.Fol.fll1Check (Bench.circ $k)) = true"
done
