#!/usr/bin/env bash
# Benchmark the 'memoize FOLLOW only' variant (Bench.Memo.Fol) against the library default.
#   usage: ./bench3.sh [circ|grow]
set -u
cd "$(dirname "$0")" || exit 1
fam="${1:-circ}"
LIMIT=60
run_one () {
  name="$1"; body="$2"; out="$3"
  { echo "import $IMP"; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp3_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp3_$name.lean" >"$out/$name.log" 2>"$out/$name.time"
  read -r el rc < "$out/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-22s %10s\n' "$name" "$tot" | tee -a "$out/summary.txt"
}
lake build Bench.Circ Bench.MemoGrow > /dev/null 2>&1 || { echo 'bench build failed'; exit 1; }
IMP=Bench.Circ
OUT=bench3-results-$fam; mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
for k in 2 4 8; do
  if [ "$fam" = circ ]; then
    ref="(Bench.circ $k).ll1Check = true"; fol="(Bench.Memo.Fol.fll1Check (Bench.circ $k)) = true"
    refn="(Bench.circ $k).follow 7 (LTok.tok ($k+4)) = true"
    foln="(Bench.Memo.Fol.fFollow (Bench.circ $k) 7 (LTok.tok ($k+4))) = true"
  else
    ref="(Bench.grow $k).ll1Check = true"; fol="(Bench.Memo.Fol.fll1Check (Bench.grow $k)) = true"
    refn="(Bench.grow $k).follow (Bench.top $k) LTok.eof = true"
    foln="(Bench.Memo.Fol.fFollow (Bench.grow $k) (Bench.top $k) LTok.eof) = true"
  fi
  run_one "ref_ll1check_$k" "$ref" "$OUT"
  run_one "fol_ll1check_$k" "$fol" "$OUT"
  run_one "ref_follow_$k" "$refn" "$OUT"
  run_one "fol_follow_$k" "$foln" "$OUT"
done
