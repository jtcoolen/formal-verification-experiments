#!/usr/bin/env bash
# Shipped (memoized FOLLOW) vs reference (all-iterP) on every grammar of the development.
set -u
cd "$(dirname "$0")" || exit 1
LIMIT=120
OUT=bench5-results; mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
IMP=Bench.Ref
run_one () {
  name="$1"; body="$2"
  { echo "import $IMP"; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp5_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp5_$name.lean" >"$OUT/$name.log" 2>"$OUT/$name.time"
  read -r el rc < "$OUT/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-26s %10s\n' "$name" "$tot" | tee -a "$OUT/summary.txt"
}
lake build Bench.Ref > /dev/null 2>&1 || { echo 'Bench.Ref failed'; exit 1; }
T=VerifiedLL1.Examples.Toy.G
CA=VerifiedLL1.Examples.Circuits.C
QC=VerifiedLL1.Examples.QCircuits.Q
run_one "toy_ref"   "(Bench.Ref.rll1Check $T) = true"
run_one "toy_ship"  "($T).ll1Check = true"
run_one "circ_ref"  "(Bench.Ref.rll1Check $CA) = true"
run_one "circ_ship" "($CA).ll1Check = true"
run_one "qcirc_ref" "(Bench.Ref.rll1Check $QC) = true"
run_one "qcirc_ship" "($QC).ll1Check = true"
for k in 8 16 24; do
  run_one "circ${k}_ref"  "(Bench.Ref.rll1Check (Bench.circ $k)) = true"
  run_one "circ${k}_ship" "(Bench.circ $k).ll1Check = true"
done
