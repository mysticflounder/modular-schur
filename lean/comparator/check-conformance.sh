#!/usr/bin/env bash
# Offline pre-flight for the comparator auditability gate. This does NOT replace
# a real leanprover/comparator run (which re-exports the closure through the
# nanoda and Lean default kernels and checks statement identity between the two
# modules — see comparator/README.md and .github/workflows/comparator.yml). It
# is the cheap check every commit can run:
#
#   1. Build the two comparator modules:
#        Challenge — mathlib-only sorry stubs (must elaborate w/ Mathlib alone)
#        Solution  — project proofs discharging each stub, under the SAME bare
#                    (Headline.) theorem names the comparator config lists
#   2. Run the axiom audit: every Solution theorem's #print axioms closure must
#      be a subset of {propext, Classical.choice, Quot.sound}.
#
# Statement identity between Challenge and Solution is checked by the real
# comparator run, not here. Exits 0 iff both modules build and every listed
# theorem is axiom-clean.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"            # the lean/ directory (holds lakefile.toml)
cd "$LEAN_ROOT"

NAMES="$(grep -cE '^#print axioms' comparator/axiom-audit.lean || true)"

echo "== building Challenge / Solution =="
if command -v lake-build >/dev/null 2>&1; then
  lake-build Challenge Solution
else
  # Hosted CI does not install the developer's global lean-usage wrapper.
  lake build Challenge Solution
fi

echo "== axiom audit (Solution theorems) =="
OUT="$(mktemp "${TMPDIR:-/tmp}/comparator-audit.XXXXXX")"
trap 'rm -f "$OUT"' EXIT
lake env lean comparator/axiom-audit.lean >"$OUT" 2>&1 || {
  echo "FAIL: axiom-audit.lean errored (renamed theorem? library not built?)" >&2
  cat "$OUT" >&2
  exit 1
}

fail=0
if grep -Eiq "sorryAx|unknown identifier|unknown constant|error:" "$OUT"; then
  echo "FAIL: audit reported sorry/error:" >&2
  grep -Ei "sorryAx|unknown identifier|unknown constant|error:" "$OUT" >&2
  fail=1
fi
if grep -Eq 'Lean\.ofReduce|Lean\.trustCompiler|\._native\.[^.[:space:]]+\.ax_' "$OUT"; then
  echo "FAIL: a Solution theorem uses native evaluation; not permitted in this comparator set." >&2
  fail=1
fi

GOT="$(grep -Fc "depend" "$OUT" || true)"
if [[ "$GOT" -ne "$NAMES" ]]; then
  echo "FAIL: expected $NAMES axiom reports, got $GOT." >&2
  fail=1
fi

if [[ "$fail" -ne 0 ]]; then
  cat "$OUT" >&2
  exit 1
fi

echo "OK: $NAMES comparator theorems build and are axiom-clean"
echo "    (subset of {propext, Classical.choice, Quot.sound}; no sorryAx, no native_decide)."
echo "    Statement identity (Challenge ≡ Solution) is verified by the leanprover/comparator run."
