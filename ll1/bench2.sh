#!/usr/bin/env bash
# Benchmark the analyses on the scaled circuit family (k qubit tokens).
#   usage: ./bench2.sh ref | ./bench2.sh memo
set -u
cd "$(dirname "$0")" || exit 1
flavor="${1:-ref}"
OUT="bench2-results-$flavor"
mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
LIMIT=60
IMP=Bench.Circ
stmt () {
  case "$flavor:$1" in
    ref:nullable)  echo "(Bench.circ $2).nullable 1 = true";;
    ref:follow)    echo "(Bench.circ $2).follow 7 (LTok.tok ($2+4)) = true";;
    ref:ll1check)  echo "(Bench.circ $2).ll1Check = true";;
    memo:nullable) echo "(Bench.Memo.mNull (Bench.circ $2) 1) = true";;
    memo:follow)   echo "(Bench.Memo.mFollow (Bench.circ $2) 7 (LTok.tok ($2+4))) = true";;
    memo:ll1check) echo "(Bench.Memo.mll1Check (Bench.circ $2)) = true";;
  esac
}
run_one () {
  name="$1"; body="$2"
  { echo "import $IMP"; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp2_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp2_$name.lean" >"$OUT/$name.log" 2>"$OUT/$name.time"
  read -r el rc < "$OUT/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-20s %10s\n' "$name" "$tot" | tee -a "$OUT/summary.txt"
}
lake build Bench.Circ Bench.MemoGrow > /dev/null 2>&1 || { echo 'bench modules failed to build'; exit 1; }
for what in nullable follow ll1check; do
  for k in 2 4 8; do
    run_one "${what}_$k" "$(stmt "$what" "$k")"
  done
done
