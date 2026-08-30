import ModularSchur.TauClosure

/-!
# Residue-axis cover certificates

This file isolates the proof schema used by the dyadic residue-axis
certificates.  The computational certificates provide:

* a cover obtained from one coordinate axis, possibly after translating raw
  axis classes to kept reduced-class dominators; and
* a packing with one representative above each occupied coordinate residue,
  with no two packed points lying in any single available axis class.

The theorem below says that these two certificates meet by weak duality, so the
axis-cover number is exactly the size of the occupied coordinate projection.
-/

namespace ModularSchur.ResidueAxis

open Finset
open ModularSchur.TauClosure

variable {α ι ρ : Type*} [DecidableEq α] [DecidableEq ρ]

/-- Occupied residues of `X` on coordinate axis `h`. -/
def pi_h (X : Finset α) (coord : ι → α → ρ) (h : ι) : Finset ρ :=
  X.image (coord h)

/-- A coordinate-axis certificate cover for fragment family `frags`.

The selected classes `C` are available fragments, every available fragment is
contained in the ambient fiber `X`, `C` covers `X`, and the selected cover has
the size of the occupied `h`-projection.
-/
structure WholeAxisCover
    (frags : Finset (Finset α)) (X : Finset α) (coord : ι → α → ρ)
    (h : ι) (C : Finset (Finset α)) : Prop where
  sub_frags : C ⊆ frags
  frags_subset_fiber : frags.biUnion id ⊆ X
  covers_fiber : X ⊆ C.biUnion id
  card_eq_projection : C.card = (pi_h X coord h).card

/-- Raw coordinate-axis classes may be removed by dominated-class reduction.
This certificate says that every raw class is contained in some kept selected
class, so the selected reduced classes still cover the whole fiber.

The cardinality hypothesis is deliberately an inequality: after dominated-class
translation, several raw classes may collapse to the same kept class.  Together
with a projection-sized packing, `≤ |pi_h(X)|` is enough for exactness. -/
structure RawAxisCover
    (frags : Finset (Finset α)) (X : Finset α) (coord : ι → α → ρ)
    (h : ι) (raw C : Finset (Finset α)) : Prop where
  sub_frags : C ⊆ frags
  frags_subset_fiber : frags.biUnion id ⊆ X
  raw_covers_fiber : X ⊆ raw.biUnion id
  raw_dominated : ∀ R ∈ raw, ∃ F ∈ C, R ⊆ F
  cover_card_le_projection : C.card ≤ (pi_h X coord h).card

/-- A packing lower-bound certificate: packed points are covered by the fragment
family, and each fragment contains at most one packed point. -/
structure AxisPacking (frags : Finset (Finset α)) (P : Finset α) : Prop where
  subset_union : P ⊆ frags.biUnion id
  at_most_one : ∀ F ∈ frags, (P ∩ F).card ≤ 1

/-- The residue-axis cover number is the ordinary finite set-cover number for
the available axis classes. -/
noncomputable def axis_cover (frags : Finset (Finset α)) : ℕ :=
  tau frags

/-- The finite set of cardinalities attained by packings against the available
axis classes. -/
noncomputable def packingCardSet (frags : Finset (Finset α)) : Finset ℕ := by
  classical
  exact (Finset.range ((frags.biUnion id).card + 1)).filter
    (fun n => ∃ P : Finset α, AxisPacking frags P ∧ P.card = n)

/-- The finite set of attainable packing cardinalities is nonempty: the empty
packing always has size `0`. -/
theorem packingCardSet_nonempty (frags : Finset (Finset α)) :
    (packingCardSet frags).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  rw [packingCardSet, Finset.mem_filter]
  refine ⟨by simp, ?_⟩
  refine ⟨∅, ?_⟩
  constructor
  · constructor
    · simp
    · intro F hF
      simp
  · simp

/-- The maximum cardinality of a packing against the available axis classes. -/
noncomputable def maxPacking (frags : Finset (Finset α)) : ℕ :=
  (packingCardSet frags).max' (packingCardSet_nonempty frags)

theorem wholeAxisCover_isCover
    {frags : Finset (Finset α)} {X : Finset α} {coord : ι → α → ρ}
    {h : ι} {C : Finset (Finset α)}
    (hC : WholeAxisCover frags X coord h C) :
    IsCoverOf frags C := by
  refine ⟨hC.sub_frags, ?_⟩
  intro x hx
  exact hC.covers_fiber (hC.frags_subset_fiber hx)

theorem rawAxisCover_isCover
    {frags : Finset (Finset α)} {X : Finset α} {coord : ι → α → ρ}
    {h : ι} {raw C : Finset (Finset α)}
    (hR : RawAxisCover frags X coord h raw C) :
    IsCoverOf frags C := by
  refine ⟨hR.sub_frags, ?_⟩
  intro x hx
  have hxX : x ∈ X := hR.frags_subset_fiber hx
  obtain ⟨R, hRmem, hxR⟩ := Finset.mem_biUnion.mp (hR.raw_covers_fiber hxX)
  obtain ⟨F, hFmem, hRF⟩ := hR.raw_dominated R hRmem
  exact Finset.mem_biUnion.mpr ⟨F, hFmem, hRF hxR⟩

theorem axis_cover_le_of_cover_card
    {frags C : Finset (Finset α)} {k : ℕ}
    (hC : IsCoverOf frags C) (hcard : C.card = k) :
    axis_cover frags ≤ k := by
  unfold axis_cover tau
  exact Nat.sInf_le ⟨C, hC, hcard⟩

theorem axis_cover_le_of_cover_card_le
    {frags C : Finset (Finset α)} {k : ℕ}
    (hC : IsCoverOf frags C) (hcard : C.card ≤ k) :
    axis_cover frags ≤ k := by
  exact le_trans (axis_cover_le_of_cover_card hC rfl) hcard

/-- A packing certificate gives a lower bound on the minimum cover size. -/
theorem packing_card_le_axis_cover
    (frags : Finset (Finset α)) (P : Finset α)
    (hP : AxisPacking frags P) :
    P.card ≤ axis_cover frags := by
  unfold axis_cover tau
  apply le_csInf (minCoverExists frags)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑P =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (hP.subset_union a.2))),
        (Classical.choose_spec
          (Finset.mem_biUnion.mp (hScov (hP.subset_union a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in :=
    (Classical.choose_spec
      (Finset.mem_biUnion.mp (hScov (hP.subset_union ha)))).2
  have hb_in :=
    (Classical.choose_spec
      (Finset.mem_biUnion.mp (hScov (hP.subset_union hb)))).2
  have hb_in' :
      b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (hP.subset_union ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec
      (Finset.mem_biUnion.mp (hScov (hP.subset_union ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (hP.at_most_one _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- Any packing size is bounded above by the maximum packing number. -/
theorem packing_card_le_maxPacking
    (frags : Finset (Finset α)) (P : Finset α)
    (hP : AxisPacking frags P) :
    P.card ≤ maxPacking frags := by
  classical
  change P.card ≤ (packingCardSet frags).max' (packingCardSet_nonempty frags)
  exact Finset.le_max' _ _ (by
    rw [packingCardSet, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.succ_le_succ (Finset.card_le_card hP.subset_union))
    · exact ⟨P, hP, rfl⟩)

/-- The maximum packing number is bounded above by the residue-axis cover
number. -/
theorem maxPacking_le_axis_cover
    (frags : Finset (Finset α)) :
    maxPacking frags ≤ axis_cover frags := by
  classical
  change (packingCardSet frags).max' (packingCardSet_nonempty frags) ≤ axis_cover frags
  refine Finset.max'_le (s := packingCardSet frags)
    (H := packingCardSet_nonempty frags) (x := axis_cover frags) ?_
  intro n hn
  rw [packingCardSet, Finset.mem_filter] at hn
  rcases hn with ⟨hn_range, hn_pack⟩
  rcases hn_pack with ⟨P, hP, rfl⟩
  exact packing_card_le_axis_cover frags P hP

/-- Whole-axis cover plus one-per-residue packing proves exact axis cover.

The cover hypothesis supplies the upper bound `≤ |pi_h(X)|`; the packing
hypothesis supplies the lower bound `≥ |pi_h(X)|`. -/
theorem axis_cover_eq_projection_card_of_wholeAxis
    {frags : Finset (Finset α)} {X P : Finset α} {coord : ι → α → ρ}
    {h : ι} {C : Finset (Finset α)}
    (hC : WholeAxisCover frags X coord h C)
    (hP : AxisPacking frags P)
    (hPcard : P.card = (pi_h X coord h).card) :
    axis_cover frags = (pi_h X coord h).card := by
  apply le_antisymm
  · exact axis_cover_le_of_cover_card (wholeAxisCover_isCover hC) hC.card_eq_projection
  · rw [← hPcard]
    exact packing_card_le_axis_cover frags P hP

/-- A raw-axis cover whose selected reduced classes have size at most
`|pi_h(X)|`, plus a projection-sized packing, proves exact axis cover. -/
theorem axis_cover_eq_projection_card_of_rawAxis
    {frags : Finset (Finset α)} {X P : Finset α} {coord : ι → α → ρ}
    {h : ι} {raw C : Finset (Finset α)}
    (hR : RawAxisCover frags X coord h raw C)
    (hP : AxisPacking frags P)
    (hPcard : P.card = (pi_h X coord h).card) :
    axis_cover frags = (pi_h X coord h).card := by
  apply le_antisymm
  · exact axis_cover_le_of_cover_card_le (rawAxisCover_isCover hR)
      hR.cover_card_le_projection
  · rw [← hPcard]
    exact packing_card_le_axis_cover frags P hP

/-- A raw-axis cover and a packing of the same size prove exact axis cover.

This is the shape used by the chunked deficit-growth rows: the selected cover
and the witness packing have matching cardinality, even when that cardinality
is strictly smaller than the occupied coordinate projection. -/
theorem axis_cover_eq_card_of_rawAxis_and_packing
    {frags : Finset (Finset α)} {X P : Finset α} {coord : ι → α → ρ}
    {h : ι} {raw C : Finset (Finset α)}
    (hR : RawAxisCover frags X coord h raw C)
    (hP : AxisPacking frags P)
    (hCP : C.card = P.card) :
    axis_cover frags = C.card := by
  apply le_antisymm
  · exact axis_cover_le_of_cover_card (rawAxisCover_isCover hR) rfl
  · rw [hCP]
    exact packing_card_le_axis_cover frags P hP

/-- A direct cover certificate and a packing of the same size prove exact axis
cover.

This is the shape used when the certificate pair already provides a direct
cover of the fragment family, so no raw-dominated intermediate is needed. -/
theorem axis_cover_eq_card_of_cover_and_packing
    {frags C : Finset (Finset α)} {P : Finset α}
    (hC : IsCoverOf frags C)
    (hP : AxisPacking frags P)
    (hCP : C.card = P.card) :
    axis_cover frags = C.card := by
  apply le_antisymm
  · exact axis_cover_le_of_cover_card hC rfl
  · rw [hCP]
    exact packing_card_le_axis_cover frags P hP

/-- A direct cover certificate and a packing of the same size saturate both the
minimum cover number and the maximum packing number. -/
theorem axis_cover_eq_maxPacking_of_cover_and_packing
    {frags C : Finset (Finset α)} {P : Finset α}
    (hC : IsCoverOf frags C)
    (hP : AxisPacking frags P)
    (hCP : C.card = P.card) :
    axis_cover frags = maxPacking frags := by
  apply le_antisymm
  · exact le_trans (axis_cover_le_of_cover_card hC rfl) (by
      rw [hCP]
      exact packing_card_le_maxPacking frags P hP)
  · exact maxPacking_le_axis_cover frags

/-- A whole-axis cover and a projection-sized packing saturate both the minimum
cover number and the maximum packing number. -/
theorem axis_cover_eq_maxPacking_of_wholeAxis
    {frags : Finset (Finset α)} {X P : Finset α} {coord : ι → α → ρ}
    {h : ι} {C : Finset (Finset α)}
    (hC : WholeAxisCover frags X coord h C)
    (hP : AxisPacking frags P)
    (hPcard : P.card = (pi_h X coord h).card) :
    axis_cover frags = maxPacking frags := by
  refine axis_cover_eq_maxPacking_of_cover_and_packing
    (wholeAxisCover_isCover hC) hP ?_
  rw [hC.card_eq_projection, ← hPcard]

/-- A raw-axis cover and a packing of the same size saturate both the minimum
cover number and the maximum packing number. -/
theorem axis_cover_eq_maxPacking_of_rawAxis_and_packing
    {frags : Finset (Finset α)} {X P : Finset α} {coord : ι → α → ρ}
    {h : ι} {raw C : Finset (Finset α)}
    (hR : RawAxisCover frags X coord h raw C)
    (hP : AxisPacking frags P)
    (hCP : C.card = P.card) :
    axis_cover frags = maxPacking frags := by
  exact axis_cover_eq_maxPacking_of_cover_and_packing
    (rawAxisCover_isCover hR) hP hCP

end ModularSchur.ResidueAxis
