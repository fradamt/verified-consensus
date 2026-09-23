#!/usr/bin/env bash
# Verify the published state of decoupled-consensus-model end to end.
#
# What an auditor learns from each step:
#   (a) lake build       -- the model, statements, internal vocabulary, proofs,
#                            and witnesses all elaborate and kernel-check under
#                            the pinned Lean/mathlib toolchain. Skipped with
#                            --quick (use only when .lake/build is already
#                            fresh, e.g. right after CI built it).
#   (b) review boundary   -- the manual review surface (DecoupledConsensusModel
#                            + DecoupledConsensusStatements, reached from
#                            DecoupledConsensusStatements) contains no internal
#                            predicate, proof, or fixture module, and no
#                            statements file is left out of that closure.
#   (c) statement reachability -- every declaration in DecoupledConsensusStatements
#                            is actually used by the two reviewed bundle roots
#                            (or is on the explicit, hand-checked helper
#                            allowlist), so there is no second, unreviewed
#                            statement collection hiding in the surface.
#   (d) review surface shape -- the generic bundle and result records expose
#                            exactly the expected fields, and no legacy
#                            statement declaration has crept back onto the
#                            surface.
#   (e) review axioms     -- the exact concreteConsensus type and the closed
#                            review theorem and every internal
#                            theorem it is built from depend on nothing beyond
#                            propext, Classical.choice, and Quot.sound: no
#                            project axiom and no unresolved `sorry`.
#   (f) sorry/admit scan  -- a second, independent check that none of the five
#                            library directories contains the literal tokens
#                            `sorry` or `admit`, as a backstop to (e) in case
#                            the axiom script's own coverage is ever wrong.
#
# Usage: scripts/verify.sh [--quick]
#   --quick   skip the `lake build` step (assumes .lake/build is already
#             current for the five libraries below).
#
# Exits 0 iff every step (run or not skipped) passed.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

LIBRARIES=(
  DecoupledConsensusModel
  DecoupledConsensusStatements
  DecoupledConsensusInternal
  DecoupledConsensusProofs
  DecoupledConsensusWitnesses
)
ALLOWED_AXIOMS=(propext Classical.choice Quot.sound)

quick=0
while (($#)); do
  case "$1" in
    --quick)
      quick=1
      shift
      ;;
    -h|--help)
      echo "usage: scripts/verify.sh [--quick]"
      exit 0
      ;;
    *)
      echo "unknown argument: $1" >&2
      echo "usage: scripts/verify.sh [--quick]" >&2
      exit 2
      ;;
  esac
done

# --- step implementations -------------------------------------------------
# Each step function is self-contained: it disables -e for its own body so a
# failing command is reported and does not abort the remaining steps, then
# returns 0 (pass) or 1 (fail) explicitly.

step_build() {
  set +e
  lake build "${LIBRARIES[@]}"
  local rc=$?
  set -e
  return "$rc"
}

step_boundary() {
  set +e
  ruby scripts/check-review-boundary.rb
  local rc1=$?
  ruby scripts/check-review-boundary.rb --self-test
  local rc2=$?
  set -e
  [[ $rc1 -eq 0 && $rc2 -eq 0 ]]
}

step_reachability() {
  local out rc
  set +e
  out="$(lake env lean scripts/StatementReachability.lean 2>&1)"
  rc=$?
  set -e
  echo "$out"
  if [[ $rc -ne 0 ]]; then
    echo "  StatementReachability.lean exited $rc" >&2
    return 1
  fi
  if ! grep -q 'STATEMENT_UNREACHABLE_COUNT 0' <<<"$out"; then
    echo "  expected 'STATEMENT_UNREACHABLE_COUNT 0' in the output above" >&2
    return 1
  fi
  return 0
}

step_shape() {
  local out rc
  set +e
  out="$(lake env lean scripts/ReviewSurfaceShape.lean 2>&1)"
  rc=$?
  set -e
  echo "$out"
  if [[ $rc -ne 0 ]]; then
    echo "  ReviewSurfaceShape.lean exited $rc" >&2
    return 1
  fi
  return 0
}

# Check a single `'name' depends on axioms: [a, b, c]` line from
# ReviewAxioms.lean against the allowed axiom set.
check_axiom_line() {
  local line="$1" bad=0 list ax
  list="${line#*[}"
  list="${list%]*}"
  IFS=',' read -ra axioms <<<"$list"
  for ax in "${axioms[@]}"; do
    ax="$(echo "$ax" | xargs)"
    case "$ax" in
      propext|Classical.choice|Quot.sound) ;;
      *)
        echo "  unexpected axiom '$ax' in: $line" >&2
        bad=1
        ;;
    esac
  done
  return "$bad"
}

step_axioms() {
  local out rc bad=0 line seen=0
  set +e
  out="$(lake env lean scripts/ReviewAxioms.lean 2>&1)"
  rc=$?
  set -e
  echo "$out"
  if [[ $rc -ne 0 ]]; then
    echo "  ReviewAxioms.lean exited $rc" >&2
    return 1
  fi
  # A literal sorryAx anywhere (in an axiom list or otherwise) is disqualifying.
  if grep -q 'sorryAx' <<<"$out"; then
    echo "  sorryAx present in the axiom report" >&2
    bad=1
  fi
  while IFS= read -r line; do
    [[ "$line" == *"depends on axioms:"* ]] || continue
    seen=$((seen + 1))
    check_axiom_line "$line" || bad=1
  done <<<"$out"
  if [[ $seen -eq 0 ]]; then
    echo "  no 'depends on axioms' line found; ReviewAxioms.lean output format may have changed" >&2
    bad=1
  fi
  return "$bad"
}

step_no_sorry() {
  local found
  found="$(grep -rnE -w --include='*.lean' 'sorry|admit' "${LIBRARIES[@]}" || true)"
  if [[ -n "$found" ]]; then
    echo "$found" >&2
    return 1
  fi
  return 0
}

# --- driver -----------------------------------------------------------------

overall=0

run_step() {
  local label="$1"
  shift
  echo "--- $label ---"
  if "$@"; then
    printf 'PASS  %s\n' "$label"
  else
    printf 'FAIL  %s\n' "$label"
    overall=1
  fi
}

if [[ $quick -eq 1 ]]; then
  echo "SKIP  lake build (--quick)"
else
  run_step "lake build (five libraries)" step_build
fi
run_step "review boundary (check-review-boundary.rb + --self-test)" step_boundary
run_step "statement reachability (StatementReachability.lean)" step_reachability
run_step "review surface shape (ReviewSurfaceShape.lean)" step_shape
run_step "review axioms (ReviewAxioms.lean: ${ALLOWED_AXIOMS[*]} only)" step_axioms
run_step "no sorry/admit in library sources" step_no_sorry

echo
if [[ $overall -eq 0 ]]; then
  echo "verify.sh: ALL CHECKS PASSED"
else
  echo "verify.sh: FAILURES PRESENT" >&2
fi
exit "$overall"
