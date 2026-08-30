import ModularSchur.ResidueAxis
import ModularSchur.SameSupportFiber

/-!
# Anchored Exact Transversal

This file formalizes the lightweight AET witness schema from
`docs/proofs/anchored-exact-transversal.md` together with the theorem that a
cover/packing witness of equal size saturates the residue-axis cover number.

The full existence theorem (Theorem B) is **REFUTED**, not open: AET fails on the
certified dyadic PID-failing fiber `n = 880, d₀ = 35200, P = (121, 125, 256)`
(packing 48, cover 50).  See `docs/proofs/dyadic-aet-failure-n880-2026-06-21.md`.
This file packages only the Theorem-A direction (AET witness ⇒ exactness) used by
the dyadic residue-coordinate program, which is unaffected.
-/

namespace ModularSchur.AnchoredExactTransversal

open Classical
open Finset
open ModularSchur.ResidueAxis
open ModularSchur.SameSupportFiber
open ModularSchur.TauClosure
open ModularSchur.CoordinateUnion

universe u v w

variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

/-- The coordinate clique at axis `g` and residue `r` inside a same-support
fiber `X_P`. -/
noncomputable def coordClique (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) (g r : ℕ) : Finset (AtomClass cell.F) :=
  (X_P cell.label cell.F P).filter (fun A => SameSupportCell.rho_g cell g A = r)

/-- The full coordinate-clique family of a same-support fiber. -/
noncomputable def coordCliques (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) : Finset (Finset (AtomClass cell.F)) :=
  P.biUnion (fun g =>
    (pi_h (X_P cell.label cell.F P) (SameSupportCell.rho_g cell) g).image
      (coordClique cell P g))

/-- Every coordinate clique lies inside the same-support fiber it comes from. -/
theorem coordClique_subset_X_P (cell : NormalizedCell α ι)
    [Fintype (AtomClass cell.F)] (P : Finset ℕ) (g r : ℕ) :
    coordClique cell P g r ⊆ X_P cell.label cell.F P := by
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- Every clique in the coordinate-clique family is contained in `X_P`. -/
theorem coordCliques_subset_X_P (cell : NormalizedCell α ι)
    [Fintype (AtomClass cell.F)] (P : Finset ℕ) :
    ∀ C ∈ coordCliques cell P, C ⊆ X_P cell.label cell.F P := by
  intro C hC
  rcases Finset.mem_biUnion.mp hC with ⟨g, hg, hCg⟩
  rcases Finset.mem_image.mp hCg with ⟨r, hr, rfl⟩
  exact coordClique_subset_X_P cell P g r

/-- An atom class in the same-support fiber witnesses that the corresponding
coordinate clique is present in the full coordinate-clique family. -/
theorem coordClique_mem_coordCliques_of_class_witness
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {g r : ℕ} (hg : g ∈ P) {A : AtomClass cell.F}
    (hA : A ∈ X_P cell.label cell.F P)
    (hRho : SameSupportCell.rho_g cell g A = r) :
    coordClique cell P g r ∈ coordCliques cell P := by
  unfold coordCliques
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨g, hg, ?_⟩
  refine Finset.mem_image.mpr ?_
  refine ⟨r, ?_, rfl⟩
  exact Finset.mem_image.mpr ⟨A, hA, hRho⟩

/-- A raw representative in the same-support fiber witnesses that the
corresponding coordinate clique is present in the full coordinate-clique
family. -/
theorem coordClique_mem_coordCliques_of_witness
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {g r : ℕ} (hg : g ∈ P) {a : α}
    (hSupport : supportLabels cell.label cell.F a = P)
    (hRho : cell.rho g a = r) :
    coordClique cell P g r ∈ coordCliques cell P := by
  have hX : atomClass cell.F a ∈ X_P cell.label cell.F P := by
    have hSuppAtom :
        atomSupportLabels cell.label cell.F (atomClass cell.F a) = P := by
      simpa [atomSupportLabels_mk] using hSupport
    simp [X_P, hSuppAtom]
  have hr : SameSupportCell.rho_g cell g (atomClass cell.F a) = r := by
    simpa [SameSupportCell.rho_g_mk] using hRho
  exact coordClique_mem_coordCliques_of_class_witness cell P hg hX hr

/-- Coordinate fiber on a finite carrier, expressed through a carrier-side
rho table. -/
noncomputable def carrierCoordClique {β : Type w} [Fintype β]
    (rho : ℕ → β → ℕ) (g r : ℕ) : Finset β :=
  Finset.univ.filter (fun b => rho g b = r)

/-- If a finite carrier maps onto the scanner same-support fiber and its rho
table agrees with scanner rho after transport, then carrier coordinate fibers
transport exactly to scanner coordinate cliques. -/
theorem carrierCoordClique_image_eq_coordClique
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {β : Type w} [Fintype β]
    (φ : β → AtomClass cell.F) (rho : ℕ → β → ℕ)
    (g r : ℕ)
    (hmem : ∀ b, φ b ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ b, φ b = A)
    (hrho : ∀ b, SameSupportCell.rho_g cell g (φ b) = rho g b) :
    (carrierCoordClique rho g r).image φ = coordClique cell P g r := by
  classical
  apply le_antisymm
  · intro A hA
    rcases Finset.mem_image.mp hA with ⟨b, hb, rfl⟩
    have hRho : SameSupportCell.rho_g cell g (φ b) = r := by
      exact (hrho b).trans (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨hmem b, hRho⟩
  · intro A hA
    have hAX : A ∈ X_P cell.label cell.F P := (Finset.mem_filter.mp hA).1
    have hAr : SameSupportCell.rho_g cell g A = r :=
      (Finset.mem_filter.mp hA).2
    rcases hsurj A hAX with ⟨b, hb⟩
    refine Finset.mem_image.mpr ⟨b, ?_, hb⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · exact Finset.mem_univ b
    · calc
        rho g b = SameSupportCell.rho_g cell g (φ b) := (hrho b).symm
        _ = SameSupportCell.rho_g cell g A := by rw [hb]
        _ = r := hAr

/-- A support witness for a transported point implies its atom class lies in
the corresponding same-support fiber. -/
theorem atomClass_mem_X_P_of_support
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {β : Type w} (pointAtom : β → α)
    (hsupport : ∀ b, supportLabels cell.label cell.F (pointAtom b) = P) :
    ∀ b, atomClass cell.F (pointAtom b) ∈ X_P cell.label cell.F P := by
  intro b
  have h := hsupport b
  simpa [X_P, mem_X_P_iff, atomSupportLabels_mk] using h

/-- If every raw same-support atom has a preimage in a finite carrier, then the
transported atom classes cover the entire scanner same-support fiber. -/
theorem atomClass_surjective_on_X_P_of_support
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {β : Type w} (pointAtom : β → α)
    (hsurj : ∀ a : α, supportLabels cell.label cell.F a = P → ∃ b, pointAtom b = a) :
    ∀ A ∈ X_P cell.label cell.F P, ∃ b, atomClass cell.F (pointAtom b) = A := by
  intro A hA
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  have hSupport : supportLabels cell.label cell.F a = P := by
    simpa [X_P, mem_X_P_iff, atomSupportLabels_mk] using hA
  rcases hsurj a hSupport with ⟨b, hb⟩
  exact ⟨b, by simp [hb]⟩

/-- The image of a point-indexed coordinate fiber is the corresponding scanner
coordinate clique once the point atoms cover the same-support fiber. -/
theorem atomClass_pointCoordClique_image_eq_coordClique
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {β : Type w} [Fintype β]
    (pointAtom : β → α)
    (hsupport : ∀ b, supportLabels cell.label cell.F (pointAtom b) = P)
    (hsurj : ∀ a : α, supportLabels cell.label cell.F a = P → ∃ b, pointAtom b = a)
    (g r : ℕ) :
    (carrierCoordClique (fun g b => cell.rho g (pointAtom b)) g r).image
        (fun b => atomClass cell.F (pointAtom b)) =
      coordClique cell P g r := by
  exact carrierCoordClique_image_eq_coordClique cell P
    (fun b => atomClass cell.F (pointAtom b))
    (fun g b => cell.rho g (pointAtom b))
    g r
    (atomClass_mem_X_P_of_support cell P pointAtom hsupport)
    (atomClass_surjective_on_X_P_of_support cell P pointAtom hsurj)
    (by
      intro b
      simp [SameSupportCell.rho_g_mk])

/-- Lightweight AET witness: a selected coordinate-clique cover, together with
an anchored packing of the same cardinality. -/
structure AETWitness (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) where
  D : Finset (Finset (AtomClass cell.F))
  T : Finset (AtomClass cell.F)
  D_subset : D ⊆ coordCliques cell P
  cover : X_P cell.label cell.F P ⊆ D.biUnion id
  anchor : T ⊆ D.biUnion id
  independent : ∀ C ∈ coordCliques cell P, (T ∩ C).card ≤ 1
  card_eq : D.card = T.card

/-- Carrier-side AET witness: the anchors live on a finite carrier `β` and are
transported into `AtomClass` by an injective map `φ`. -/
structure CarrierAETWitness (cell : NormalizedCell α ι)
    [Fintype (AtomClass cell.F)] (β : Type*) [DecidableEq β]
    (P : Finset ℕ) where
  D : Finset (Finset (AtomClass cell.F))
  T : Finset β
  φ : β → AtomClass cell.F
  D_subset : D ⊆ coordCliques cell P
  cover : X_P cell.label cell.F P ⊆ D.biUnion id
  T_subset_XP : ∀ b ∈ T, φ b ∈ X_P cell.label cell.F P
  independent : ∀ C ∈ coordCliques cell P, (T.image φ ∩ C).card ≤ 1
  phi_injective : Function.Injective φ
  card_eq : D.card = T.card

/-- The selected AET cliques form a cover of the coordinate-clique family. -/
theorem isCoverOf_of_AET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (W : AETWitness cell P) :
    IsCoverOf (coordCliques cell P) W.D := by
  refine ⟨W.D_subset, ?_⟩
  intro A hA
  rcases Finset.mem_biUnion.mp hA with ⟨C, hC, hAC⟩
  exact W.cover ((coordCliques_subset_X_P cell P C hC) hAC)

/-- The AET anchors form a packing against all coordinate cliques. -/
theorem axisPacking_of_AET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (W : AETWitness cell P) :
    AxisPacking (coordCliques cell P) W.T := by
  have hTsub : W.T ⊆ (coordCliques cell P).biUnion id := by
    intro A hA
    have hAD : A ∈ W.D.biUnion id := W.anchor hA
    rcases Finset.mem_biUnion.mp hAD with ⟨C, hC, hAC⟩
    exact Finset.mem_biUnion.mpr ⟨C, W.D_subset hC, hAC⟩
  exact ⟨hTsub, W.independent⟩

/-- AET witness plus the cover/packing exact-duality schema gives exact axis
cover. -/
theorem axis_cover_eq_witness_card_of_AET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (W : AETWitness cell P) :
    axis_cover (coordCliques cell P) = W.D.card := by
  exact axis_cover_eq_card_of_cover_and_packing
    (isCoverOf_of_AET cell W) (axisPacking_of_AET cell W) W.card_eq

/-- Nonempty AET predicate. -/
def hasAET (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) : Prop :=
  Nonempty (AETWitness cell P)

/-- Theorem A in proposition form: if a fiber has an AET witness, then the
coordinate-clique cover number is realized by some witness cardinality. -/
theorem axis_cover_eq_card_of_hasAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (h : hasAET cell P) :
    ∃ W : AETWitness cell P, axis_cover (coordCliques cell P) = W.D.card := by
  rcases h with ⟨W⟩
  exact ⟨W, axis_cover_eq_witness_card_of_AET cell W⟩

/-- Clean AET statement: if a fiber has an AET witness, the cover and packing
numbers coincide on the coordinate-clique family. -/
theorem axis_cover_eq_maxPacking_of_hasAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (h : hasAET cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  rcases h with ⟨W⟩
  exact axis_cover_eq_maxPacking_of_cover_and_packing
    (isCoverOf_of_AET cell W) (axisPacking_of_AET cell W) W.card_eq

/-- If a selected set of anchors is pairwise separated on every axis in `P`,
then it is independent against the full coordinate-clique family. -/
theorem independent_of_axis_injective
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} {T : Finset (AtomClass cell.F)}
    (hsep : ∀ g ∈ P, ∀ A ∈ T, ∀ B ∈ T,
      A ≠ B → SameSupportCell.rho_g cell g A ≠ SameSupportCell.rho_g cell g B) :
    ∀ C ∈ coordCliques cell P, (T ∩ C).card ≤ 1 := by
  intro C hC
  rcases Finset.mem_biUnion.mp hC with ⟨g, hg, hCg⟩
  rcases Finset.mem_image.mp hCg with ⟨r, hr, rfl⟩
  apply Finset.card_le_one.mpr
  intro A hA B hB
  rcases Finset.mem_inter.mp hA with ⟨hAT, hAC⟩
  rcases Finset.mem_inter.mp hB with ⟨hBT, hBC⟩
  have hAr : SameSupportCell.rho_g cell g A = r := by
    exact (Finset.mem_filter.mp hAC).2
  have hBr : SameSupportCell.rho_g cell g B = r := by
    exact (Finset.mem_filter.mp hBC).2
  have hEq : SameSupportCell.rho_g cell g A = SameSupportCell.rho_g cell g B := by
    calc
      SameSupportCell.rho_g cell g A = r := hAr
      _ = SameSupportCell.rho_g cell g B := hBr.symm
  by_contra hne
  exact (hsep g hg A hAT B hBT hne) hEq

/-- Carrier-side version of `independent_of_axis_injective`, transported
through an injective image into `AtomClass`. -/
theorem independent_of_axis_injective_image
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β]
    {P : Finset ℕ} {T : Finset β}
    (φ : β → AtomClass cell.F)
    (hsep : ∀ g ∈ P, ∀ a ∈ T, ∀ b ∈ T,
      a ≠ b → SameSupportCell.rho_g cell g (φ a) ≠ SameSupportCell.rho_g cell g (φ b)) :
    ∀ C ∈ coordCliques cell P, ((T.image φ) ∩ C).card ≤ 1 := by
  intro C hC
  have hsep' : ∀ g ∈ P, ∀ A ∈ T.image φ, ∀ B ∈ T.image φ,
      A ≠ B → SameSupportCell.rho_g cell g A ≠ SameSupportCell.rho_g cell g B := by
    intro g hg A hA B hB hAB
    rcases Finset.mem_image.mp hA with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hB with ⟨b, hb, rfl⟩
    exact hsep g hg a ha b hb (by
      intro hab
      exact hAB (by simp [hab]))
  exact independent_of_axis_injective cell (P := P) (T := T.image φ) hsep' C hC

/-- On a nodup list, `getD` is injective on bounded indices. -/
theorem list_getD_injective_of_nodup {β : Type*} [DecidableEq β]
    (l : List β) (d : β) (h : l.Nodup) :
    ∀ {i j : ℕ}, i < l.length → j < l.length → l.getD i d = l.getD j d → i = j := by
  intro i j hi hj hEq
  have hget : l[i] = l[j] := by
    simpa [List.getD_eq_getElem, hi, hj] using hEq
  exact (List.Nodup.getElem_inj_iff (l := l) h).1 hget

/-- Transport a carrier-side witness into the `AtomClass`-valued witness
record. -/
noncomputable def carrier_witness_to_AETWitness
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β]
    {P : Finset ℕ} (W : CarrierAETWitness cell β P) :
    AETWitness cell P :=
  { D := W.D,
    T := W.T.image W.φ,
    D_subset := W.D_subset,
    cover := W.cover,
    anchor := by
      intro A hA
      rcases Finset.mem_image.mp hA with ⟨b, hb, rfl⟩
      exact W.cover (W.T_subset_XP b hb)
    independent := W.independent,
    card_eq := by
      calc
        W.D.card = W.T.card := W.card_eq
        _ = (W.T.image W.φ).card := (Finset.card_image_of_injective W.T W.phi_injective).symm }

/-- Carrier-side witness card exactness. -/
theorem axis_cover_eq_witness_card_of_CarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β]
    {P : Finset ℕ} (W : CarrierAETWitness cell β P) :
    axis_cover (coordCliques cell P) = W.D.card := by
  exact axis_cover_eq_witness_card_of_AET cell (carrier_witness_to_AETWitness cell W)

/-- Carrier-side AET witness predicate. -/
def hasCarrierAET (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (β : Type*) [DecidableEq β] (P : Finset ℕ) : Prop :=
  Nonempty (CarrierAETWitness cell β P)

/-- A carrier-side witness already gives the actual `AETWitness`. -/
theorem hasAET_of_hasCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β]
    {P : Finset ℕ} (h : hasCarrierAET cell β P) :
    hasAET cell P := by
  rcases h with ⟨W⟩
  exact ⟨carrier_witness_to_AETWitness cell W⟩

/-- Carrier-side witness card exactness. -/
theorem axis_cover_eq_card_of_hasCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β]
    {P : Finset ℕ} (h : hasCarrierAET cell β P) :
    ∃ W : CarrierAETWitness cell β P, axis_cover (coordCliques cell P) = W.D.card := by
  rcases h with ⟨W⟩
  exact ⟨W, axis_cover_eq_witness_card_of_CarrierAET cell W⟩

/-- Carrier-side witness exactness on the max-packing side. -/
theorem axis_cover_eq_maxPacking_of_hasCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {β : Type*} [DecidableEq β]
    {P : Finset ℕ} (h : hasCarrierAET cell β P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  exact axis_cover_eq_maxPacking_of_hasAET cell (hasAET_of_hasCarrierAET cell h)

end ModularSchur.AnchoredExactTransversal
