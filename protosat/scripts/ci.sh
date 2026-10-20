#!/usr/bin/env bash
#
# ProtSat verification gate (roadmap stage 7).
#
# Every check here corresponds to a claim the README makes:
#
#   * the build is the proof check - every theorem, including the kernel-checked gates, is
#     re-elaborated from source;
#   * the source scan is the no-admissions check - no sorry, no native_decide, no user axiom;
#   * the axiom audit is the trust-boundary check - only propext, Classical.choice, Quot.sound;
#   * the theorem inventory is a regression floor - a deleted guarantee fails CI;
#   * the demo run is the executability check - honest executions, independent certificate
#     replay, and one printed line per contract verdict;
#   * the budgets are the resource claim: build and demo must stay inside stated limits.
#
# Run it directly (protosat/scripts/ci.sh) or through .github/workflows/ci.yml.
#
set -u

cd "$(dirname "$0")/.." || exit 1

THEOREM_FLOOR=2880
BUILD_BUDGET=1500
DEMO_BUDGET=300

pass=0
fail=0
ok() { printf 'PASS  %s\n' "$1"; pass=$((pass + 1)); }
no() { printf 'FAIL  %s\n' "$1"; fail=$((fail + 1)); }

printf 'ProtSat verification gate\n'
printf '%s\n' '-------------------------'

# 1. clean build -------------------------------------------------------------
t0=$(date +%s)
if lake build > /tmp/protosat-ci-build.log 2>&1; then
  t1=$(date +%s)
  dur=$((t1 - t0))
  jobs=$(sed -n 's/.*Build completed successfully (\([0-9]*\) jobs).*/\1/p' /tmp/protosat-ci-build.log | tail -1)
  if [ "$dur" -le "$BUILD_BUDGET" ]; then
    ok "lake build: $jobs jobs in $dur s (budget $BUILD_BUDGET s)"
  else
    no "lake build exceeded the budget: $dur s > $BUILD_BUDGET s"
  fi
else
  no "lake build failed"
  tail -25 /tmp/protosat-ci-build.log | sed 's/^/      /'
fi

# 2. no admissions -----------------------------------------------------------
admits=$(grep -rn --include='*.lean' -E '\bsorry\b|\bnative_decide\b' ProtSat Main.lean Axioms.lean \
  | grep -v 'nothing uses partiality or native_decide' || true)
if [ -z "$admits" ]; then
  ok "no sorry and no native_decide in any source file"
else
  no "admissions found"
  printf '%s\n' "$admits" | sed 's/^/      /'
fi
userax=$(grep -rn --include='*.lean' -E '^axiom ' ProtSat Main.lean || true)
if [ -z "$userax" ]; then
  ok "no user-declared axioms"
else
  no "user axioms declared"
  printf '%s\n' "$userax" | sed 's/^/      /'
fi

# 3. axiom audit and theorem inventory ---------------------------------------
audit=$(lake env lean Axioms.lean 2>&1 || true)
if printf '%s' "$audit" | grep -q 'OK - every theorem depends only'; then
  ok "axiom audit clean (propext, Classical.choice, Quot.sound only)"
else
  no "axiom audit flagged something"
  printf '%s\n' "$audit" | tail -15 | sed 's/^/      /'
fi
count=$(printf '%s' "$audit" | sed -n 's/.*theorems audited in ProtSat\.\*: *//p' | tr -cd '0-9')
if [ -n "$count" ] && [ "$count" -ge "$THEOREM_FLOOR" ]; then
  ok "theorem inventory: $count (floor $THEOREM_FLOOR)"
else
  no "theorem inventory: got '$count', floor is $THEOREM_FLOOR"
fi

# 4. executability and evidence replay ---------------------------------------
t0=$(date +%s)
demo=$(lake exe protosatDemo 2>/dev/null || true)
t1=$(date +%s)
dur=$((t1 - t0))
if [ -z "$demo" ]; then
  no "the demo produced no output"
elif [ "$dur" -le "$DEMO_BUDGET" ]; then
  ok "demo runs in $dur s (budget $DEMO_BUDGET s)"
else
  no "demo exceeded the budget: $dur s > $DEMO_BUDGET s"
fi

expect() {   # substring, description
  if printf '%s' "$demo" | grep -qF "$1"; then
    ok "$2"
  else
    no "$2 (missing output line: $1)"
  fi
}
expect 'BOUNDED SAFE' 'a bounded-safety verdict is produced'
expect 'ATTACK' 'an attack verdict is produced'
expect 'witness re-checked without the search: true' 'attack certificates replay without the search'
expect 'ENCODING UNSAT' 'the CNF answer is labelled as a formula fact'
expect 'UNSUPPORTED GOALS' 'a goal the encoding cannot represent is refused'
expect 'NO GOALS SELECTED' 'an empty goal set is refused'
expect 'REPRESENTABILITY OF THE VALUE DOMAIN' 'the value-domain report is printed'
expect 'value domain: complete' 'a query whose domain names every computed value says so'
expect 'value domain: GAP' 'the under-approximation is reported where the universe cannot name a computed value'
expect 'INVALID MODEL' 'a malformed model is reported with diagnostics'
expect 'checkCertificate = true' 'the independent certificate checker accepts the Lowe attack'
expect 'checkCertificate = false' 'the independent certificate checker rejects the same script on NSL'
expect 'refutation checked: true' 'a resolution refutation is checked independently of the solver'
expect 'serialized refutation checked: true' 'the refutation survives serialization and is still checked'
expect 'code decodes back to the same proof: true' 'the serialization round trip is executable'
expect 'evidence bound to a different formula rejected: true' 'evidence transplanted to another formula is rejected'
expect 'produced by the engine and checked: true' 'the resolution engine emits a refutation the independent checker accepts'
expect 'engine output survives serialization: true' 'the engine refutation round-trips through the code format and is still accepted'
expect 'derived bound ' 'the model-derived step bound is reported next to the bound the query chose'

printf '%s\n' '-------------------------'
printf '%d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ] || exit 1
printf 'ALL GATES GREEN\n'
