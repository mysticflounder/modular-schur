/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.ResidueAxis

/-!
# Axis-labelled finite covers

This file connects a finite family whose blocks retain axis labels to the extensional
fragment families used by `TauClosure.tau` and `ResidueAxis.axis_cover`.  Equal block
neighbourhoods are identified by `Finset.image`; the minimum cover and packing constraints
are unchanged.

It also isolates labels with a private point.  Such labels occur in every labelled cover,
and deleting all points covered by them gives an exact additive decomposition of the cover
number.  This is seed deletion, not exhaustive forced peeling after repeated restriction.
-/

namespace ModularSchur.AxisLabelledCover

open Classical Finset
open ModularSchur.ResidueAxis
open ModularSchur.TauClosure

universe u v

variable {α : Type u} {ι : Type v} [DecidableEq α] [DecidableEq ι]

/-- A selection of labels covers a labelled block family when it uses available labels and
covers every point occurring in an available block. -/
def IsLabelCover (labels : Finset ι) (neighbourhood : ι → Finset α)
    (selected : Finset ι) : Prop :=
  selected ⊆ labels ∧ labels.biUnion neighbourhood ⊆ selected.biUnion neighbourhood

/-- The family obtained after identifying labels with equal point neighbourhoods. -/
def extensionalImage (labels : Finset ι) (neighbourhood : ι → Finset α) :
    Finset (Finset α) :=
  labels.image neighbourhood

/-- Minimum cardinality of a labelled cover. -/
noncomputable def labelCoverNumber (labels : Finset ι) (neighbourhood : ι → Finset α) :
    ℕ :=
  sInf {n | ∃ selected : Finset ι,
    IsLabelCover labels neighbourhood selected ∧ selected.card = n}

omit [DecidableEq ι] in
/-- The union of an extensional image is the union of the labelled family. -/
@[simp]
theorem biUnion_extensionalImage (labels : Finset ι) (neighbourhood : ι → Finset α) :
    (extensionalImage labels neighbourhood).biUnion id =
      labels.biUnion neighbourhood := by
  ext x
  simp [extensionalImage]

omit [DecidableEq ι] in
/-- The full label set is a labelled cover. -/
theorem labelCover_self (labels : Finset ι) (neighbourhood : ι → Finset α) :
    IsLabelCover labels neighbourhood labels :=
  ⟨Subset.rfl, Subset.rfl⟩

omit [DecidableEq ι] in
/-- Every labelled cover bounds the labelled cover number from above. -/
theorem labelCoverNumber_le_card {labels selected : Finset ι}
    {neighbourhood : ι → Finset α}
    (hselected : IsLabelCover labels neighbourhood selected) :
    labelCoverNumber labels neighbourhood ≤ selected.card :=
  Nat.sInf_le ⟨selected, hselected, rfl⟩

omit [DecidableEq ι] in
/-- The minimum labelled-cover cardinality is attained. -/
theorem labelCoverNumber_attained (labels : Finset ι) (neighbourhood : ι → Finset α) :
    ∃ selected : Finset ι,
      IsLabelCover labels neighbourhood selected ∧
        selected.card = labelCoverNumber labels neighbourhood := by
  have hne :
      ({n | ∃ selected : Finset ι,
        IsLabelCover labels neighbourhood selected ∧ selected.card = n} : Set ℕ).Nonempty :=
    ⟨labels.card, labels, labelCover_self labels neighbourhood, rfl⟩
  exact Nat.sInf_mem hne

omit [DecidableEq ι] in
/-- A labelled cover maps to an extensional cover after duplicate neighbourhoods are
identified. -/
theorem isCoverOf_extensionalImage {labels selected : Finset ι}
    {neighbourhood : ι → Finset α}
    (hselected : IsLabelCover labels neighbourhood selected) :
    IsCoverOf (extensionalImage labels neighbourhood)
      (extensionalImage selected neighbourhood) := by
  constructor
  · intro block hblock
    rcases Finset.mem_image.mp hblock with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hselected.1 hi, rfl⟩
  · simpa only [biUnion_extensionalImage] using hselected.2

/-- The ordinary finite cover number is attained by an extensional cover. -/
theorem tau_attained (frags : Finset (Finset α)) :
    ∃ cover : Finset (Finset α), IsCoverOf frags cover ∧ cover.card = tau frags := by
  have hne :
      ({n | ∃ cover : Finset (Finset α),
        IsCoverOf frags cover ∧ cover.card = n} : Set ℕ).Nonempty :=
    ⟨frags.card, frags, ⟨Subset.rfl, Subset.rfl⟩, rfl⟩
  exact Nat.sInf_mem hne

omit [DecidableEq ι] in
/-- An extensional cover admits one representative label for each selected neighbourhood. -/
theorem exists_labelCover_card_eq_of_isCoverOf
    {labels : Finset ι} {neighbourhood : ι → Finset α}
    {cover : Finset (Finset α)}
    (hcover : IsCoverOf (extensionalImage labels neighbourhood) cover) :
    ∃ selected : Finset ι,
      IsLabelCover labels neighbourhood selected ∧ selected.card = cover.card := by
  have hsurj :
      (↑labels : Set ι).SurjOn neighbourhood (↑cover : Set (Finset α)) := by
    intro block hblock
    have hblockCover : block ∈ cover := by simpa using hblock
    rcases Finset.mem_image.mp (hcover.1 hblockCover) with ⟨i, hi, hEq⟩
    exact ⟨i, by simpa using hi, hEq⟩
  obtain ⟨selected, hselected, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn
      (f := neighbourhood) (↑labels : Set ι) cover hsurj
  refine ⟨selected, ?_, ?_⟩
  · constructor
    · simpa using hselected
    · intro x hx
      have hxExtensional :
          x ∈ (extensionalImage labels neighbourhood).biUnion id := by
        simpa only [biUnion_extensionalImage] using hx
      have hxCover : x ∈ cover.biUnion id := hcover.2 hxExtensional
      rw [← himage] at hxCover
      simpa [extensionalImage] using hxCover
  · calc
      selected.card = (selected.image neighbourhood).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ = cover.card := congrArg Finset.card himage

omit [DecidableEq ι] in
/-- Identifying equal neighbourhoods preserves the minimum cover number. -/
theorem labelCoverNumber_eq_tau_extensionalImage
    (labels : Finset ι) (neighbourhood : ι → Finset α) :
    labelCoverNumber labels neighbourhood = tau (extensionalImage labels neighbourhood) := by
  apply le_antisymm
  · obtain ⟨cover, hcover, hcard⟩ := tau_attained (extensionalImage labels neighbourhood)
    obtain ⟨selected, hselected, hselectedCard⟩ :=
      exists_labelCover_card_eq_of_isCoverOf hcover
    calc
      labelCoverNumber labels neighbourhood ≤ selected.card :=
        labelCoverNumber_le_card hselected
      _ = cover.card := hselectedCard
      _ = tau (extensionalImage labels neighbourhood) := hcard
  · obtain ⟨selected, hselected, hcard⟩ :=
      labelCoverNumber_attained labels neighbourhood
    have hExtensional := isCoverOf_extensionalImage hselected
    calc
      tau (extensionalImage labels neighbourhood) ≤
          (extensionalImage selected neighbourhood).card :=
        Nat.sInf_le ⟨extensionalImage selected neighbourhood, hExtensional, rfl⟩
      _ ≤ selected.card := Finset.card_image_le
      _ = labelCoverNumber labels neighbourhood := hcard

omit [DecidableEq ι] in
/-- Packing constraints can be checked on labels before duplicate neighbourhoods are
identified. -/
theorem axisPacking_extensionalImage_iff
    (labels : Finset ι) (neighbourhood : ι → Finset α) (packing : Finset α) :
    AxisPacking (extensionalImage labels neighbourhood) packing ↔
      packing ⊆ labels.biUnion neighbourhood ∧
        ∀ i ∈ labels, (packing ∩ neighbourhood i).card ≤ 1 := by
  constructor
  · intro hpacking
    constructor
    · simpa only [biUnion_extensionalImage] using hpacking.subset_union
    · intro i hi
      exact hpacking.at_most_one (neighbourhood i)
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · rintro ⟨hsubset, hatMostOne⟩
    constructor
    · simpa only [biUnion_extensionalImage] using hsubset
    · intro block hblock
      rcases Finset.mem_image.mp hblock with ⟨i, hi, rfl⟩
      exact hatMostOne i hi

/-- A point private to one label among the available labels. -/
def IsPrivatePoint (labels : Finset ι) (neighbourhood : ι → Finset α)
    (i : ι) (x : α) : Prop :=
  x ∈ neighbourhood i ∧
    ∀ j ∈ labels, x ∈ neighbourhood j → j = i

/-- A label with a private point. -/
def IsPrivateLabel (labels : Finset ι) (neighbourhood : ι → Finset α)
    (i : ι) : Prop :=
  ∃ x, IsPrivatePoint labels neighbourhood i x

/-- The support-one seed labels of a labelled family. -/
noncomputable def privateLabels (labels : Finset ι) (neighbourhood : ι → Finset α) :
    Finset ι :=
  labels.filter (IsPrivateLabel labels neighbourhood)

omit [DecidableEq α] [DecidableEq ι] in
@[simp]
theorem mem_privateLabels {labels : Finset ι} {neighbourhood : ι → Finset α} {i : ι} :
    i ∈ privateLabels labels neighbourhood ↔
      i ∈ labels ∧ IsPrivateLabel labels neighbourhood i := by
  simp [privateLabels]

omit [DecidableEq α] [DecidableEq ι] in
/-- Private labels are available labels. -/
theorem privateLabels_subset (labels : Finset ι) (neighbourhood : ι → Finset α) :
    privateLabels labels neighbourhood ⊆ labels := by
  intro i hi
  exact (mem_privateLabels.mp hi).1

omit [DecidableEq ι] in
/-- Every labelled cover contains every private label. -/
theorem privateLabels_subset_of_isLabelCover
    {labels selected : Finset ι} {neighbourhood : ι → Finset α}
    (hselected : IsLabelCover labels neighbourhood selected) :
    privateLabels labels neighbourhood ⊆ selected := by
  intro i hi
  obtain ⟨hiLabels, x, hxi, hprivate⟩ := mem_privateLabels.mp hi
  have hxLabels : x ∈ labels.biUnion neighbourhood :=
    Finset.mem_biUnion.mpr ⟨i, hiLabels, hxi⟩
  rcases Finset.mem_biUnion.mp (hselected.2 hxLabels) with ⟨j, hj, hxj⟩
  have hji : j = i := hprivate j (hselected.1 hj) hxj
  simpa [hji] using hj

omit [DecidableEq α] [DecidableEq ι] in
/-- Distinct private labels have distinct original neighbourhoods. -/
theorem neighbourhood_injOn_privateLabels
    (labels : Finset ι) (neighbourhood : ι → Finset α) :
    Set.InjOn neighbourhood (privateLabels labels neighbourhood) := by
  intro i hi j hj hEq
  obtain ⟨_, x, hxi, hprivate⟩ := mem_privateLabels.mp hi
  have hjLabels := (mem_privateLabels.mp hj).1
  have hxj : x ∈ neighbourhood j := by simpa [← hEq] using hxi
  exact (hprivate j hjLabels hxj).symm

omit [DecidableEq ι] in
/-- Private labels do not collapse when neighbourhoods are identified. -/
theorem card_image_privateLabels
    (labels : Finset ι) (neighbourhood : ι → Finset α) :
    ((privateLabels labels neighbourhood).image neighbourhood).card =
      (privateLabels labels neighbourhood).card :=
  Finset.card_image_of_injOn (neighbourhood_injOn_privateLabels labels neighbourhood)

/-- Points covered by a chosen seed set. -/
def coveredPoints (seeds : Finset ι) (neighbourhood : ι → Finset α) : Finset α :=
  seeds.biUnion neighbourhood

/-- A block restricted to points not covered by the chosen seeds. -/
def residualNeighbourhood (seeds : Finset ι) (neighbourhood : ι → Finset α)
    (i : ι) : Finset α :=
  neighbourhood i \ coveredPoints seeds neighbourhood

/-- Removing mandatory labels from a cover leaves a cover of the restricted residual
family. -/
theorem sdiff_isLabelCover_residual
    {labels seeds selected : Finset ι} {neighbourhood : ι → Finset α}
    (hselected : IsLabelCover labels neighbourhood selected) :
    IsLabelCover (labels \ seeds) (residualNeighbourhood seeds neighbourhood)
      (selected \ seeds) := by
  constructor
  · intro i hi
    have hiSelected := (Finset.mem_sdiff.mp hi).1
    have hiNotSeed := (Finset.mem_sdiff.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨hselected.1 hiSelected, hiNotSeed⟩
  · intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    have hxiBlock := (Finset.mem_sdiff.mp hxi).1
    have hxNotCovered := (Finset.mem_sdiff.mp hxi).2
    have hxLabels : x ∈ labels.biUnion neighbourhood :=
      Finset.mem_biUnion.mpr ⟨i, (Finset.mem_sdiff.mp hi).1, hxiBlock⟩
    rcases Finset.mem_biUnion.mp (hselected.2 hxLabels) with ⟨j, hj, hxj⟩
    have hjNotSeed : j ∉ seeds := by
      intro hjSeed
      exact hxNotCovered (Finset.mem_biUnion.mpr ⟨j, hjSeed, hxj⟩)
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_sdiff.mpr ⟨hj, hjNotSeed⟩,
        Finset.mem_sdiff.mpr ⟨hxj, hxNotCovered⟩⟩

/-- A cover of the seed-deleted residual family extends to a cover of the original
family after the seeds are restored. -/
theorem union_isLabelCover_of_residual
    {labels seeds residualCover : Finset ι} {neighbourhood : ι → Finset α}
    (hseedLabels : seeds ⊆ labels)
    (hresidual :
      IsLabelCover (labels \ seeds) (residualNeighbourhood seeds neighbourhood)
        residualCover) :
    IsLabelCover labels neighbourhood (seeds ∪ residualCover) := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hiSeed | hiResidual
    · exact hseedLabels hiSeed
    · exact (Finset.mem_sdiff.mp (hresidual.1 hiResidual)).1
  · intro x hx
    by_cases hxCovered : x ∈ coveredPoints seeds neighbourhood
    · rcases Finset.mem_biUnion.mp hxCovered with ⟨i, hiSeed, hxi⟩
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_union_left _ hiSeed, hxi⟩
    · rcases Finset.mem_biUnion.mp hx with ⟨i, hiLabels, hxi⟩
      have hiNotSeed : i ∉ seeds := by
        intro hiSeed
        exact hxCovered (Finset.mem_biUnion.mpr ⟨i, hiSeed, hxi⟩)
      have hxResidualLabels :
          x ∈ (labels \ seeds).biUnion (residualNeighbourhood seeds neighbourhood) :=
        Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_sdiff.mpr ⟨hiLabels, hiNotSeed⟩,
            Finset.mem_sdiff.mpr ⟨hxi, hxCovered⟩⟩
      rcases Finset.mem_biUnion.mp (hresidual.2 hxResidualLabels) with
        ⟨j, hjResidual, hxj⟩
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_union_right _ hjResidual, (Finset.mem_sdiff.mp hxj).1⟩

/-- Deleting any set of labels that occurs in every cover gives an exact additive
decomposition of the labelled cover number. -/
theorem labelCoverNumber_eq_card_add_residual
    (labels seeds : Finset ι) (neighbourhood : ι → Finset α)
    (hseedLabels : seeds ⊆ labels)
    (hmandatory : ∀ selected,
      IsLabelCover labels neighbourhood selected → seeds ⊆ selected) :
    labelCoverNumber labels neighbourhood =
      seeds.card +
        labelCoverNumber (labels \ seeds) (residualNeighbourhood seeds neighbourhood) := by
  apply le_antisymm
  · obtain ⟨residualCover, hresidual, hresidualCard⟩ :=
      labelCoverNumber_attained (labels \ seeds)
        (residualNeighbourhood seeds neighbourhood)
    have hcover := union_isLabelCover_of_residual hseedLabels hresidual
    have hdisjoint : Disjoint seeds residualCover := by
      refine Finset.disjoint_left.mpr ?_
      intro i hiSeed hiResidual
      exact (Finset.mem_sdiff.mp (hresidual.1 hiResidual)).2 hiSeed
    calc
      labelCoverNumber labels neighbourhood ≤ (seeds ∪ residualCover).card :=
        labelCoverNumber_le_card hcover
      _ = seeds.card + residualCover.card := Finset.card_union_of_disjoint hdisjoint
      _ = seeds.card +
          labelCoverNumber (labels \ seeds)
            (residualNeighbourhood seeds neighbourhood) := by rw [hresidualCard]
  · obtain ⟨selected, hselected, hselectedCard⟩ :=
      labelCoverNumber_attained labels neighbourhood
    have hseeds := hmandatory selected hselected
    have hresidual := sdiff_isLabelCover_residual (seeds := seeds) hselected
    have hresidualLe := labelCoverNumber_le_card hresidual
    calc
      seeds.card +
          labelCoverNumber (labels \ seeds)
            (residualNeighbourhood seeds neighbourhood) ≤
          seeds.card + (selected \ seeds).card :=
        Nat.add_le_add_left hresidualLe seeds.card
      _ = (seeds ∪ (selected \ seeds)).card :=
        (Finset.card_union_of_disjoint Finset.disjoint_sdiff).symm
      _ = selected.card := congrArg Finset.card (Finset.union_sdiff_of_subset hseeds)
      _ = labelCoverNumber labels neighbourhood := hselectedCard

/-- The extensional residual family after deleting all points covered by private labels. -/
noncomputable def privateResidualImage
    (labels : Finset ι) (neighbourhood : ι → Finset α) : Finset (Finset α) :=
  extensionalImage (labels \ privateLabels labels neighbourhood)
    (residualNeighbourhood (privateLabels labels neighbourhood) neighbourhood)

/-- Exact support-one seed decomposition for the extensional cover number. -/
theorem axis_cover_extensionalImage_eq_privateLabels_add_residual
    (labels : Finset ι) (neighbourhood : ι → Finset α) :
    axis_cover (extensionalImage labels neighbourhood) =
      (privateLabels labels neighbourhood).card +
        axis_cover (privateResidualImage labels neighbourhood) := by
  have hdecomp := labelCoverNumber_eq_card_add_residual labels
    (privateLabels labels neighbourhood) neighbourhood
    (privateLabels_subset labels neighbourhood)
    (fun _ hcover ↦ privateLabels_subset_of_isLabelCover hcover)
  simpa [axis_cover, privateResidualImage, labelCoverNumber_eq_tau_extensionalImage]
    using hdecomp

end ModularSchur.AxisLabelledCover
