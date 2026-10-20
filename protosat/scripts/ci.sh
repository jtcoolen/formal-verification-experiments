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
# ---------------------------------------------------------------------------
# What this script assumes about the machine (step 0 checks these rather than
# trusting them):
#
#   * lake, lean, git and curl are on PATH.  lean and lake normally come from
#     elan; the installer the elan README gives today is
#     https://elan.lean-lang.org/elan-init.sh, and elan picks the toolchain
#     from protosat/lean-toolchain by walking up from the current directory.
#   * Mathlib's prebuilt .oleans are already in the workspace, under
#     .lake/packages/mathlib/.lake/build/lib.  They arrive via
#     "lake exe cache get", which .github/workflows/ci.yml runs before this
#     script.  Building Mathlib v4.34.1 from source takes hours, so a run that
#     starts doing that is an ENVIRONMENT failure, not a build failure, and is
#     reported as such rather than letting the time budget misreport it.
#   * The log directory is writable.  Default /tmp; override with PROTSAT_CI_LOGDIR.
#   * GNU userland is NOT required.  Only portable constructs are used
#     (date +%s, sed -n 's///p', grep -E/-F/--include, tr -cd, printf), checked
#     against BSD grep 2.6.0-FreeBSD and bash 3.2 (the macOS /bin/bash) as well
#     as the GNU coreutils that ubuntu-latest ships.
#     The one GNU-ism kept from the previous version is grep --include, which
#     BSD grep 2.6.0-FreeBSD also supports.
#   * The budgets are developer-machine numbers (see README "Build and run").
#     A 4-core CI runner is not a 10-core laptop, so every number can be
#     overridden in the environment without editing this file:
#     PROTSAT_CI_BUILD_BUDGET, PROTSAT_CI_DEMO_BUDGET, PROTSAT_CI_THEOREM_FLOOR,
#     PROTSAT_CI_MATHLIB_FLOOR, PROTSAT_CI_COLD_DEPS_MAX, PROTSAT_CI_ALLOW_COLD_MATHLIB.
#
# Exit codes: 0 every gate green; 1 a gate failed; 3 the environment is wrong,
# which means the gates never ran and nothing about the proofs was established.
# ---------------------------------------------------------------------------

set -u
export LC_ALL=C

cd "$(dirname "$0")/.." || exit 1

THEOREM_FLOOR=${PROTSAT_CI_THEOREM_FLOOR:-2880}
BUILD_BUDGET=${PROTSAT_CI_BUILD_BUDGET:-1500}
DEMO_BUDGET=${PROTSAT_CI_DEMO_BUDGET:-300}
# How many Mathlib .oleans count as "the cache is in place".  A full Mathlib is ~8.5k.
MATHLIB_FLOOR=${PROTSAT_CI_MATHLIB_FLOOR:-1000}

LOGDIR=${PROTSAT_CI_LOGDIR:-/tmp}
BUILD_LOG="$LOGDIR/protosat-ci-build.log"
DEMO_LOG="$LOGDIR/protosat-ci-demo.log"
DEMO_ERR="$LOGDIR/protosat-ci-demo.err"
AUDIT_LOG="$LOGDIR/protosat-ci-audit.log"

pass=0
fail=0
ok() { printf 'PASS  %s\n' "$1"; pass=$((pass + 1)); }
no() { printf 'FAIL  %s\n' "$1"; fail=$((fail + 1)); }

printf 'ProtSat verification gate\n'
printf '%s\n' '-------------------------'

# An environment problem: the gate never got to test anything, so it must not be
# reported as a proof failure.  Distinct exit code, and the message says what to
# do about it.
env_problem() {
  printf '\n' >&2
  printf 'ENVIRONMENT PROBLEM - the gate did not run.\n' >&2
  printf '%s\n' "$@" >&2
  printf 'Nothing here says anything about the proofs.  Fix the machine and re-run.\n' >&2
  printf 'To build Mathlib from source anyway: PROTSAT_CI_ALLOW_COLD_MATHLIB=1 ./scripts/ci.sh\n' >&2
  exit 3
}

# 0. environment preflight ---------------------------------------------------
missing=''
for tool in lake lean git curl sed grep find date; do
  command -v "$tool" >/dev/null 2>&1 || missing="$missing $tool"
done
if [ -n "$missing" ]; then
  env_problem "not on PATH:$missing" \
    "On a CI runner the Lean toolchain comes from elan; see .github/workflows/ci.yml." \
    "Locally: install elan from https://elan.lean-lang.org/elan-init.sh, then run this from protosat/."
fi
if [ ! -w "$LOGDIR" ]; then
  env_problem "the log directory $LOGDIR is not writable (set PROTSAT_CI_LOGDIR)."
fi
# lake --version is the cheapest probe that also makes elan fetch the toolchain.
if ! lake_ver=$(lake --version 2>&1); then
  env_problem "lake --version failed; the pinned toolchain is not usable." "$lake_ver"
fi
if ! lean_ver=$(lean --version 2>&1); then
  env_problem "lean --version failed; the pinned toolchain is not usable." "$lean_ver"
fi
printf 'ENV   %s\n' "$lake_ver"
printf 'ENV   %s\n' "$lean_ver"

MATHLIB_SRC=.lake/packages/mathlib
if [ ! -f "$MATHLIB_SRC/lakefile.lean" ]; then
  env_problem "Mathlib is not resolved in this workspace ($MATHLIB_SRC/lakefile.lean is missing)." \
    "Run: cd protosat && lake exe cache get   (lake clones the pinned mathlib4 revision itself)."
fi
mathlib_oleans=$(find "$MATHLIB_SRC/.lake/build" -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')
[ -n "$mathlib_oleans" ] || mathlib_oleans=0
if [ "$mathlib_oleans" -lt "$MATHLIB_FLOOR" ]; then
  if [ -n "${PROTSAT_CI_ALLOW_COLD_MATHLIB:-}" ]; then
    printf 'ENV   Mathlib has only %s prebuilt .oleans (floor %s): building from source, as asked.\n' \
      "$mathlib_oleans" "$MATHLIB_FLOOR"
  else
    env_problem "Mathlib prebuilt .oleans are not in place: found $mathlib_oleans, floor is $MATHLIB_FLOOR." \
      "lake build would now compile Mathlib from source (hours), which is not what BUILD_BUDGET=$BUILD_BUDGET s assumes." \
      "Fetch the cache first:  cd protosat && lake exe cache get"
  fi
else
  printf 'ENV   Mathlib prebuilt .oleans present: %s\n' "$mathlib_oleans"
fi

# 1. clean build -------------------------------------------------------------
t0=$(date +%s)
if lake build > "$BUILD_LOG" 2>&1; then
  t1=$(date +%s)
  dur=$((t1 - t0))
  jobs=$(sed -n 's/.*Build completed successfully (\([0-9]*\) jobs).*/\1/p' "$BUILD_LOG" | tail -1)
  if [ -z "$jobs" ]; then
    # lake prints "Nothing to build." when every target trace already matches.
    if grep -qF 'Nothing to build.' "$BUILD_LOG"; then jobs=0; else jobs='?'; fi
  fi
  # Did the build RE-ELABORATE a dependency from source?  lake logs one line per executed
  # job, and the FACET matters.  "Built Mathlib.Algebra.Group.Basic" (or the same name with
  # :lean) is a Lean module being elaborated - that is what a Mathlib cache miss looks like.
  # "Built Batteries.Tactic.Alias:c.o" is only the C object being compiled, and mathlib's
  # cache serves .olean and .trace artifacts but NOT .o files, so every fresh runner
  # legitimately recompiles the C parts of its transitive dependencies.  Counting those as a
  # cache failure is a false positive: the first real CI run (Linux, 2026-10-20) reported 893
  # of them while all 8548 .oleans were present and no Lean module was re-elaborated.  So the
  # facet-less count is the gate and the C-object count is information.
  deps_re='Built (Mathlib|Batteries|Aesop|Qq|ImportGraph|ProofWidgets|LeanSearchClient|Plausible|Cli)[A-Za-z0-9_.]*(:lean)?([[:space:]]|$)'
  deps_built=$(grep -cE "$deps_re" "$BUILD_LOG" 2>/dev/null)
  [ -n "$deps_built" ] || deps_built=0
  cobjects=$(grep -cE 'Built (Mathlib|Batteries|Aesop|Qq|ImportGraph|ProofWidgets|LeanSearchClient|Plausible|Cli)[A-Za-z0-9_.]*:c\.(o|dynlib|a)([[:space:]]|$)' "$BUILD_LOG" 2>/dev/null)
  [ -n "$cobjects" ] || cobjects=0
  own_built=$(grep -cE 'Built (ProtSat|Main)[A-Za-z0-9_.]*(:lean)?([[:space:]]|$)' "$BUILD_LOG" 2>/dev/null)
  [ -n "$own_built" ] || own_built=0
  COLD_DEPS_MAX=${PROTSAT_CI_COLD_DEPS_MAX:-200}
  if [ "$cobjects" -gt 0 ]; then
    printf 'ENV   %s dependency C objects compiled (expected on a fresh runner: the Mathlib cache holds .olean and .trace, not .o)\n' "$cobjects"
  fi
  if [ "$deps_built" -gt 0 ]; then
    printf 'WARN  %s dependency Lean modules re-elaborated from source (Mathlib cache incomplete; limit %s)\n' \
      "$deps_built" "$COLD_DEPS_MAX"
  fi
  if [ "$deps_built" -gt "$COLD_DEPS_MAX" ] && [ -z "${PROTSAT_CI_ALLOW_COLD_MATHLIB:-}" ]; then
    sample=$(grep -E "$deps_re" "$BUILD_LOG" 2>/dev/null | sed -n '1,5p')
    env_problem "lake build re-elaborated $deps_built dependency Lean modules (limit $COLD_DEPS_MAX): the Mathlib cache was not usable." \
      "That is an environment failure, not a proof failure - the build gate tested nothing." \
      "Run: cd protosat && lake exe cache get   (then re-run this script)." \
      "First offending lines:" "$sample"
  fi
  if [ "$dur" -le "$BUILD_BUDGET" ]; then
    ok "lake build: $jobs jobs in $dur s (budget $BUILD_BUDGET s; $own_built ProtSat modules re-elaborated)"
  else
    no "lake build exceeded the budget: $dur s > $BUILD_BUDGET s"
    tail -25 "$BUILD_LOG" | sed 's/^/      /'
  fi
else
  no "lake build failed"
  tail -25 "$BUILD_LOG" | sed 's/^/      /'
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
lake env lean Axioms.lean > "$AUDIT_LOG" 2>&1
audit=$(cat "$AUDIT_LOG" 2>/dev/null || true)
if [ -z "$audit" ]; then
  no "axiom audit produced no output (lake env lean Axioms.lean failed silently)"
  count=''
else
  if printf '%s' "$audit" | grep -q 'OK - every theorem depends only'; then
    ok "axiom audit clean (propext, Classical.choice, Quot.sound only)"
  else
    no "axiom audit flagged something"
    printf '%s\n' "$audit" | tail -15 | sed 's/^/      /'
  fi
  count=$(printf '%s' "$audit" | sed -n 's/.*theorems audited in ProtSat\.\*: *//p' | tr -cd '0-9')
fi
if [ -n "$count" ] && [ "$count" -ge "$THEOREM_FLOOR" ]; then
  ok "theorem inventory: $count (floor $THEOREM_FLOOR)"
else
  no "theorem inventory: got '$count', floor is $THEOREM_FLOOR"
fi

# 4. executability and evidence replay ---------------------------------------
t0=$(date +%s)
if lake exe protosatDemo > "$DEMO_LOG" 2> "$DEMO_ERR"; then demo_status=0; else demo_status=$?; fi
t1=$(date +%s)
dur=$((t1 - t0))
demo=$(cat "$DEMO_LOG" 2>/dev/null || true)
if [ -z "$demo" ]; then
  no "the demo produced no output (lake exe protosatDemo exited $demo_status)"
  tail -25 "$DEMO_ERR" | sed 's/^/      /'
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
expect 'certificate: 138 integers, 21 resolution lines' 'the analyser emits a serialized refutation certificate for a real query'
expect 'the independent checker accepts the certificate: true' 'the emitted certificate is accepted by the checker, with no solver replay'
expect 'the same bytes against the leaky variant of the model, rejected: true' 'the certificate is bound to the formula it was emitted for'
expect 'the producer re-run emits exactly these bytes: true' 'the embedded certificate is reproducible by the producer that emitted it'
expect 'derived bound ' 'the model-derived step bound is reported next to the bound the query chose'
expect 'attackFoundP = false' 'the pruned enumerator decides safety at the model-derived bound'

printf '%s\n' '-------------------------'
printf '%d passed, %d failed\n' "$pass" "$fail"
printf 'logs: %s\n' "$BUILD_LOG"
[ "$fail" -eq 0 ] || exit 1
printf 'ALL GATES GREEN\n'
