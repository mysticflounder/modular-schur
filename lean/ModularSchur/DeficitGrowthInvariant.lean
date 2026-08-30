import ModularSchur.ResidueAxis

/-!
# Deficit-growth invariant carrier

This file records the arithmetic skeleton isolated in the C2 note:
the baseline corner-cluster failures carry the support pattern
`25, 27, 121, 2^k` with `k ≥ 5`.

The predicate is intentionally small. It gives us a Lean-side handle on the
support pattern, without pretending that the full normalized-cell residue
histogram has already been formalized.

Caveat (2026-07-26): the arithmetic skeleton recorded above is accurate, but the
C2 *invariant* it was isolated from does not exist — no `(n, d₀, P)`-level
quantity can separate AET-holding from AET-failing cells, since the same
`(d₀, P)` holds at `n = 1760` and fails at `n = 880`.  See
`docs/deficit-growth-aet-invariant-candidate.md` and
`docs/proofs/dyadic-aet-failure-n880-2026-06-21.md`.  Read this file as a support
predicate, not as a carrier for a separating invariant.
-/

namespace ModularSchur.DeficitGrowth

open Finset

/-- Baseline support-side corner-cluster skeleton from the C2 note. -/
structure CornerClusterSkeleton (P : Finset ℕ) : Prop where
  has_25 : 25 ∈ P
  has_27 : 27 ∈ P
  has_121 : 121 ∈ P
  has_pow2 : ∃ k, 5 ≤ k ∧ 2 ^ k ∈ P

def cornerCluster330P : Finset ℕ := ({25, 27, 32, 121} : Finset ℕ)

def cornerCluster660P : Finset ℕ := ({25, 27, 64, 121} : Finset ℕ)

theorem cornerCluster330P_skeleton : CornerClusterSkeleton cornerCluster330P := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  refine ⟨5, by decide, by decide⟩

theorem cornerCluster660P_skeleton : CornerClusterSkeleton cornerCluster660P := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  refine ⟨6, by decide, by decide⟩

theorem cornerCluster330P_support_pattern :
    25 ∈ cornerCluster330P ∧ 27 ∈ cornerCluster330P ∧ 121 ∈ cornerCluster330P := by
  exact ⟨cornerCluster330P_skeleton.has_25, cornerCluster330P_skeleton.has_27,
    cornerCluster330P_skeleton.has_121⟩

theorem cornerCluster660P_support_pattern :
    25 ∈ cornerCluster660P ∧ 27 ∈ cornerCluster660P ∧ 121 ∈ cornerCluster660P := by
  exact ⟨cornerCluster660P_skeleton.has_25, cornerCluster660P_skeleton.has_27,
    cornerCluster660P_skeleton.has_121⟩

end ModularSchur.DeficitGrowth
