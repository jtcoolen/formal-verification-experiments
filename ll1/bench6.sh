#!/usr/bin/env bash
# The objective's specified family (A0 -> eps, A(i+1) -> Ai Ai) at depths 8, 12, 16:
# shipped code (memoized FOLLOW) vs the all-iterP reference.
set -u
cd "$(dirname "$0")" || exit 1
LIMIT=60
OUT=bench6-results; mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
run_one () {
  name="$1"; imp="$2"; body="$3"
  { echo "import $imp"; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp6_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp6_$name.lean" >"$OUT/$name.log" 2>"$OUT/$name.time"
  read -r el rc < "$OUT/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-24s %10s\n' "$name" "$tot" | tee -a "$OUT/summary.txt"
}
lake build Bench.Ref Bench.Grow > /dev/null 2>&1 || { echo 'bench build failed'; exit 1; }
for d in 8 12 16; do
  run_one "grow${d}_nul_ref"  Bench.Grow "(Bench.grow $d).nullable (Bench.top $d) = true"
  run_one "grow${d}_ll1_ref"  Bench.Ref  "(Bench.Ref.rll1Check (Bench.grow $d)) = true"
  run_one "grow${d}_ll1_ship" Bench.Grow "(Bench.grow $d).ll1Check = true"
done
