/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import ModularSchur.AnchoredExactTransversal
import ModularSchur.TwoAxisStructural

/-!
# Two-axis anchored exact transversals

This module connects the abstract equal-cardinality cover/packing certificate
to the project `AETWitness` structure. The support is required to be nonempty:
only then does the coordinate-clique family necessarily cover the whole
same-support fiber.
-/

namespace ModularSchur.TwoAxisAnchoredExactTransversal

open Classical
open Finset
open ModularSchur.AnchoredExactTransversal
open ModularSchur.CoordinateUnion
open ModularSchur.ResidueAxis
open ModularSchur.SameSupportFiber
open ModularSchur.TauClosure
open ModularSchur.TwoAxisStructural

universe u v

variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

/-- If the support is nonempty, its coordinate cliques cover the entire
same-support fiber. -/
theorem X_P_subset_coordCliques_biUnion_of_nonempty
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (hP : P.Nonempty) :
    X_P cell.label cell.F P ⊆ (coordCliques cell P).biUnion id := by
  classical
  intro A hA
  rcases hP with ⟨g, hg⟩
  let r := SameSupportCell.rho_g cell g A
  have hC : coordClique cell P g r ∈ coordCliques cell P :=
    coordClique_mem_coordCliques_of_class_witness cell P hg hA rfl
  have hAC : A ∈ coordClique cell P g r := by
    simp [coordClique, hA, r]
  exact Finset.mem_biUnion.mpr ⟨coordClique cell P g r, hC, hAC⟩

/-- An equal-cardinality coordinate-clique cover and packing give an anchored
exact transversal whenever the support is nonempty. -/
noncomputable def aetWitness_of_twoAxisCertificate
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (hP : P.Nonempty)
    (w : TwoAxisCertificate (coordCliques cell P)) :
    AETWitness cell P := by
  classical
  exact
    { D := w.cover
      T := w.packing
      D_subset := w.cover_is_cover.1
      cover := fun _ hA =>
        w.cover_is_cover.2
          (X_P_subset_coordCliques_biUnion_of_nonempty cell hP hA)
      anchor := fun _ hA =>
        w.cover_is_cover.2 (w.packing_is_packing.subset_union hA)
      independent := w.packing_is_packing.at_most_one
      card_eq := w.card_eq }

/-- Existence of an equal-cardinality coordinate-clique cover and packing gives
the proposition-level AET conclusion on nonempty support. -/
theorem hasAET_of_twoAxisCertificate
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (hP : P.Nonempty)
    (hw : Nonempty (TwoAxisCertificate (coordCliques cell P))) :
    hasAET cell P := by
  classical
  rcases hw with ⟨w⟩
  exact ⟨aetWitness_of_twoAxisCertificate cell hP w⟩

end ModularSchur.TwoAxisAnchoredExactTransversal
