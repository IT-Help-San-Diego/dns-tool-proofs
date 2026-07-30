#!/usr/bin/env bash
# Build gate for dns-tool-proofs.
#
# WHY THIS EXISTS: `sorry` makes any proposition compile, including a false one.
# The first false theorem in this repo (a universally-quantified flip claim,
# see Calibration.lean) sat behind a `sorry` and the build never objected —
# human review found it. `lake build` alone is therefore not a correctness gate.
#
# This script fails on any `sorry` in a proof position, and on the warning Lean
# emits for declarations that use it.
set -uo pipefail

fail=0

# 1. No `sorry` as a tactic or term (docstrings/comments are allowed to discuss it).
if grep -nE '(^|[^-])\bsorry\b' DnsToolProofs/*.lean | grep -vE '^\S+:[0-9]+:\s*(--|/-|\*)' \
     | grep -vE '`sorry`' ; then
  echo "FAIL: 'sorry' used in a proof position (above)."
  fail=1
fi

# 2. Build must succeed AND emit no 'declaration uses sorry' warning.
out=$(lake build 2>&1)
echo "$out" | grep -vE '^trace:' | tail -5
if echo "$out" | grep -qi 'declaration uses .sorry'; then
  echo "FAIL: Lean reports a declaration using sorry."
  fail=1
fi
if ! echo "$out" | grep -q 'Build completed successfully'; then
  echo "FAIL: lake build did not complete successfully."
  fail=1
fi

[ "$fail" -eq 0 ] && echo "OK: build green, no sorry in any proof."
exit "$fail"
