import ModularSchur.DeficitGrowthInvariant
import ModularSchur.AnchoredExactTransversal

/-!
# Deficit-growth restricted AET candidate

This file packages the C3 shape in Lean:

* the C2 corner-cluster skeleton is carried explicitly;
* the witness data is finite (`T : Finset _`, `frags : Finset (Finset _)`) over a
  carrier with `DecidableEq` — the carrier type itself is not assumed `Fintype`;
* the existing carrier-to-`AtomClass` bridge transports exactness back to the
  scanner-facing coordinate-clique API.

The existence of such a package is the unproved part, and the *unrestricted*
parent claim — that a dyadic PID-failing fiber always admits one — is **REFUTED**
at `n = 880, d₀ = 35200, P = (121, 125, 256)` (packing 48, cover 50); see
`docs/proofs/dyadic-aet-failure-n880-2026-06-21.md`.  That counterexample does not
itself contradict the shell below, whose `CornerClusterSkeleton` hypothesis needs
`25, 27 ∈ P`; it removes the reason to expect the shell to be inhabitable in
general.  The exactness consequences below are fully proved and reusable once a
generated row supplies the carrier data.
-/

namespace ModularSchur.DeficitGrowth

open Classical
open Finset
open ModularSchur.AnchoredExactTransversal
open ModularSchur.ResidueAxis
open ModularSchur.SameSupportFiber
open ModularSchur.TauClosure

universe u v

variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

/-- Carrier-side package for the C3 candidate.

The package stores the C2 support skeleton together with a carrier-side AET
witness.  The carrier is left abstract so the same shell can be instantiated by
`Fin n` or any other decidable finite index type.
-/
structure CornerClusterCarrierAET
    (β : Type*) [DecidableEq β]
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) where
  skeleton : CornerClusterSkeleton P
  witness : CarrierAETWitness cell β P

/-- Existence of a corner-cluster carrier package.

This is the Lean-side statement corresponding to the restricted C3 existence
candidate.
-/
def hasCornerClusterCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) : Prop :=
  ∃ (β : Type) (_inst : DecidableEq β), Nonempty (CornerClusterCarrierAET β cell P)

/-- A concrete carrier package gives a witness-cardinality statement. -/
theorem axis_cover_eq_card_of_CornerClusterCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β] {P : Finset ℕ} (h : CornerClusterCarrierAET β cell P) :
    axis_cover (coordCliques cell P) = h.witness.D.card := by
  simpa using axis_cover_eq_witness_card_of_CarrierAET cell h.witness

/-- Explicit C4 theorem candidate: the corner-cluster skeleton is a separate
hypothesis, and the carrier witness does the exactness work. -/
theorem axis_cover_eq_maxPacking_of_cornerClusterInvariant
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β] {P : Finset ℕ}
    (hs : CornerClusterSkeleton P)
    (W : CarrierAETWitness cell β P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  have _ : CornerClusterSkeleton P := hs
  exact axis_cover_eq_maxPacking_of_hasAET cell (hasAET_of_hasCarrierAET cell (h := ⟨W⟩))

/-- A concrete carrier package transports to `hasAET`. -/
theorem hasAET_of_CornerClusterCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β] {P : Finset ℕ} (h : CornerClusterCarrierAET β cell P) :
    hasAET cell P := by
  exact hasAET_of_hasCarrierAET cell (h := ⟨h.witness⟩)

/-- A concrete carrier package gives exactness on the coordinate-clique family. -/
theorem axis_cover_eq_maxPacking_of_CornerClusterCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β] {P : Finset ℕ} (h : CornerClusterCarrierAET β cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  exact axis_cover_eq_maxPacking_of_cornerClusterInvariant
    cell h.skeleton h.witness

/-- The existence form of the restricted C3 candidate already implies exactness. -/
theorem axis_cover_eq_maxPacking_of_hasCornerClusterCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (h : hasCornerClusterCarrierAET cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  rcases h with ⟨β, inst, h⟩
  rcases h with ⟨h⟩
  exact @axis_cover_eq_maxPacking_of_CornerClusterCarrierAET α ι _ _ cell _ β inst P h

end ModularSchur.DeficitGrowth
