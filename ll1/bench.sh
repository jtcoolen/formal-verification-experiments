#!/usr/bin/env bash
# Benchmark the LL(1) analyses on the growing-grammar family (A0 -> eps, A(i+1) -> Ai Ai),
# started at the deepest nonterminal so every nonterminal is reachable.
#
#   usage: ./bench.sh ref     -- the library's Fixpoint.iterP computations (reference)
#          ./bench.sh memo    -- the memoized Boolean-list backend (Bench/MemoGrow.lean)
#
# Every measurement is its own file, timed with a 60 s limit.  The reported time is the wall
# time of 'lake env lean' on that file: it covers the 'decide' tactic (which evaluates the
# decision procedure by kernel reduction) *and* the kernel check of the resulting
# declaration, which lean performs before it exits.  FAIL/TIMEOUT means the limit was hit.
set -u
cd "$(dirname "$0")" || exit 1
flavor="${1:-ref}"
OUT="bench-results-$flavor"
mkdir -p "$OUT"; rm -f "$OUT/summary.txt"
LIMIT=60
if [ "$flavor" = ref ]; then IMP=Bench.Grow; else IMP=Bench.MemoGrow; fi
stmt () {
  case "$flavor:$1" in
    ref:nullable)   echo "(Bench.grow $2).nullable (Bench.top $2) = true";;
    ref:follow)     echo "(Bench.grow $2).follow (Bench.top $2) LTok.eof = true";;
    ref:ll1check)   echo "(Bench.grow $2).ll1Check = true";;
    memo:nullable)  echo "(Bench.Memo.mNull (Bench.grow $2) (Bench.top $2)) = true";;
    memo:follow)    echo "(Bench.Memo.mFollow (Bench.grow $2) (Bench.top $2) LTok.eof) = true";;
    memo:ll1check)  echo "(Bench.Memo.mll1Check (Bench.grow $2)) = true";;
  esac
}
run_one () {
  name="$1"; body="$2"
  { echo "import $IMP"; echo 'open VerifiedLL1';
    echo 'set_option maxHeartbeats 4000000000'; echo 'set_option maxRecDepth 100000';
    echo "example : $body := by decide"; } > "Bench/Tmp_$name.lean"
  python3 bench-timeout.py $LIMIT lake env lean "Bench/Tmp_$name.lean" >"$OUT/$name.log" 2>"$OUT/$name.time"
  read -r el rc < "$OUT/$name.time"
  if [ "$rc" = "0" ]; then tot="$el"; else tot="FAIL($rc)"; fi
  printf '%-20s %10s\n' "$name" "$tot" | tee -a "$OUT/summary.txt"
}
lake build Bench.Grow Bench.MemoGrow > /dev/null 2>&1 || { echo 'bench modules failed to build'; exit 1; }
for what in nullable follow ll1check; do
  for d in 8 12 16; do
    run_one "${what}_$d" "$(stmt "$what" "$d")"
  done
done
