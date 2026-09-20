/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.CanonicalResidualCoverTransport

/-!
# Seed-aware all-but-one-axis covers

After support-one seed labels are selected, every remaining point has at least
two supported prime axes.  Consequently, all residual labels except those on
one chosen axis cover the residual family.  This file records that structural
cover statement; arithmetic formulas for the number of labels on one axis
belong to a separate module.
-/

namespace ModularSchur.CanonicalBlocks

open Classical Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- Residual labels whose prime axis is not the chosen axis. -/
def residualLabelsExceptAxis (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    Finset CanonicalBlockLabel :=
  (canonicalSeedResidualLabels n a).filter (fun label ↦ label.prime ≠ j)

/-- A residual point supports at least two distinct prime axes. -/
theorem supportedPrimes_card_ge_two_of_mem_canonicalSeedResidualPoints
    {n x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ canonicalSeedResidualPoints n a) :
    2 ≤ (supportedPrimes n x).card := by
  have hxUnit := (mem_canonicalSeedResidualPoints.mp hx).1
  have hnonempty := supportedPrimes_nonempty_of_mem_unitInterval hxUnit
  by_contra hcard
  have hcard' : (supportedPrimes n x).card ≤ 1 := by omega
  obtain ⟨p, hp⟩ := hnonempty
  have hsingleton : supportedPrimes n x = {p} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hp, ?_⟩
    intro q hq
    exact (Finset.card_le_one.mp hcard') q hq p hp
  have hpFactors := (mem_supportedPrimes.mp hp).1
  have hseed : pointLabel a p x ∈ supportOneSeedLabels n a := by
    apply mem_supportOneSeedLabels.mpr
    exact ⟨p, hpFactors, x, hxUnit, hsingleton, rfl⟩
  have hcovered : x ∈ canonicalSeedCoveredPoints n a := by
    exact Finset.mem_biUnion.mpr
      ⟨pointLabel a p x, hseed, point_mem_canonicalNeighbourhood hxUnit⟩
  exact (mem_canonicalSeedResidualPoints.mp hx).2 hcovered

/-- Every incident label at a seed-residual point is a nonseed label. -/
theorem incidentLabels_subset_canonicalSeedResidualLabels_of_mem
    {n x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ canonicalSeedResidualPoints n a) :
    incidentLabels n a x ⊆ canonicalSeedResidualLabels n a := by
  intro label hlabel
  have hdata := mem_incidentLabels.mp hlabel
  have hnotSeed : label ∉ supportOneSeedLabels n a := by
    intro hseed
    have hcovered : x ∈ canonicalSeedCoveredPoints n a := by
      exact Finset.mem_biUnion.mpr ⟨label, hseed, hdata.2⟩
    exact (mem_canonicalSeedResidualPoints.mp hx).2 hcovered
  exact Finset.mem_sdiff.mpr ⟨hdata.1, hnotSeed⟩

/-- A seed-residual point has an incident residual label off any chosen axis. -/
theorem exists_residualLabel_off_axis
    {n x : ℕ} {a : ℕ → ℕ} (j : ℕ)
    (hx : x ∈ canonicalSeedResidualPoints n a) :
    ∃ label ∈ canonicalSeedResidualLabels n a,
      label.prime ≠ j ∧
        x ∈ canonicalSeedResidualNeighbourhood n a label := by
  have hcard := supportedPrimes_card_ge_two_of_mem_canonicalSeedResidualPoints hx
  have hunit := (mem_canonicalSeedResidualPoints.mp hx).1
  have hne : ∃ p ∈ supportedPrimes n x, p ≠ j := by
    by_contra h
    push Not at h
    have hsub : supportedPrimes n x ⊆ ({j} : Finset ℕ) := by
      intro p hp
      exact Finset.mem_singleton.mpr (h p hp)
    have hle := Finset.card_le_card hsub
    simp only [card_singleton] at hle
    omega
  obtain ⟨p, hp, hpj⟩ := hne
  let label := pointLabel a p x
  have hlabel : label ∈ canonicalLabels n a := by
    exact pointLabel_mem_canonicalLabels hunit hp
  have hnotSeed : label ∉ supportOneSeedLabels n a := by
    intro hseed
    have hcovered : x ∈ canonicalSeedCoveredPoints n a := by
      exact Finset.mem_biUnion.mpr ⟨label, hseed, point_mem_canonicalNeighbourhood hunit⟩
    exact (mem_canonicalSeedResidualPoints.mp hx).2 hcovered
  have hresidualLabel : label ∈ canonicalSeedResidualLabels n a :=
    Finset.mem_sdiff.mpr ⟨hlabel, hnotSeed⟩
  have hresidualNeighbourhood :
      x ∈ canonicalSeedResidualNeighbourhood n a label := by
    exact mem_canonicalSeedResidualNeighbourhood.mpr
      ⟨point_mem_canonicalNeighbourhood hunit, hx⟩
  refine ⟨label, hresidualLabel, ?_, hresidualNeighbourhood⟩
  exact hpj

/-- All residual labels except one chosen axis cover the residual family. -/
theorem residualLabelsExceptAxis_isLabelCover
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    IsLabelCover (canonicalSeedResidualLabels n a)
      (canonicalSeedResidualNeighbourhood n a)
      (residualLabelsExceptAxis n a j) := by
  constructor
  · intro label hlabel
    exact (Finset.mem_filter.mp hlabel).1
  · intro x hx
    obtain ⟨label, hlabel, hxLabel⟩ := Finset.mem_biUnion.mp hx
    have hxResidual := (mem_canonicalSeedResidualNeighbourhood.mp hxLabel).2
    obtain ⟨offLabel, hoffLabel, hoffAxis, hxOff⟩ :=
      exists_residualLabel_off_axis j hxResidual
    exact Finset.mem_biUnion.mpr
      ⟨offLabel, Finset.mem_filter.mpr ⟨hoffLabel, hoffAxis⟩, hxOff⟩

/-- Seeds together with all nonseed labels off one axis form a labelled cover. -/
theorem allButOneAxis_isLabelCover
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    IsLabelCover (canonicalLabels n a) (canonicalNeighbourhood n a)
      (supportOneSeedLabels n a ∪ residualLabelsExceptAxis n a j) := by
  apply union_isLabelCover_of_residual
  · intro label hlabel
    obtain ⟨p, hp, x, hx, hsupport, hpoint⟩ :=
      mem_supportOneSeedLabels.mp hlabel
    have hpSupported : p ∈ supportedPrimes n x := by
      rw [hsupport]
      simp
    rw [← hpoint]
    exact pointLabel_mem_canonicalLabels hx hpSupported
  · exact residualLabelsExceptAxis_isLabelCover n a j

/-- Numerical labelled-cover bound supplied by the all-but-one-axis cover. -/
theorem labelCoverNumber_le_seed_add_residualLabelsExceptAxis
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    labelCoverNumber (canonicalLabels n a) (canonicalNeighbourhood n a) ≤
      (supportOneSeedLabels n a).card +
        (residualLabelsExceptAxis n a j).card := by
  have hcover := allButOneAxis_isLabelCover n a j
  calc
    labelCoverNumber (canonicalLabels n a) (canonicalNeighbourhood n a) ≤
        (supportOneSeedLabels n a ∪ residualLabelsExceptAxis n a j).card :=
      labelCoverNumber_le_card hcover
    _ = (supportOneSeedLabels n a).card +
        (residualLabelsExceptAxis n a j).card := by
      have hdisjoint :
          Disjoint (supportOneSeedLabels n a)
            (residualLabelsExceptAxis n a j) := by
        refine Finset.disjoint_left.mpr ?_
        intro label hseed hres
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hres).1).2 hseed
      exact Finset.card_union_of_disjoint hdisjoint

/-- Extensional canonical cover bound supplied by the all-but-one-axis cover. -/
theorem axisCover_canonicalExtensionalFamily_le_seed_add_residualLabelsExceptAxis
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    axis_cover (canonicalExtensionalFamily n a) ≤
      (supportOneSeedLabels n a).card +
        (residualLabelsExceptAxis n a j).card := by
  rw [← canonicalLabelCoverNumber_eq_axisCover]
  exact labelCoverNumber_le_seed_add_residualLabelsExceptAxis n a j

end ModularSchur.CanonicalBlocks
