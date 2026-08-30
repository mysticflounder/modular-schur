/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.CanonicalSeedTransport

/-!
# Prime multiplication for canonical residual covers

This file lifts the exact prime-multiplication residual point identity to the
residual neighbourhoods of represented canonical labels.  Only nonempty
enlarged residual neighbourhoods require old representatives; no global map on
all represented labels is needed.  The final recurrence includes both active
exponent layers and the first layer of a depth-zero inactive prime.
-/

namespace ModularSchur.CanonicalBlocks

open Classical Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- Represented labels remaining after support-one seed labels are deleted. -/
def canonicalSeedResidualLabels (n : ℕ) (a : ℕ → ℕ) :
    Finset CanonicalBlockLabel :=
  canonicalLabels n a \ supportOneSeedLabels n a

/-- A canonical block after deleting every point covered by a support-one seed
label. -/
def canonicalSeedResidualNeighbourhood (n : ℕ) (a : ℕ → ℕ)
    (label : CanonicalBlockLabel) : Finset ℕ :=
  residualNeighbourhood (supportOneSeedLabels n a)
    (canonicalNeighbourhood n a) label

private theorem isLabelCover_filter_nonempty
    {labels selected : Finset CanonicalBlockLabel}
    {neighbourhood : CanonicalBlockLabel → Finset ℕ}
    (hcover : IsLabelCover labels neighbourhood selected) :
    IsLabelCover labels neighbourhood
      (selected.filter fun label ↦ (neighbourhood label).Nonempty) := by
  constructor
  · intro label hlabel
    exact hcover.1 (Finset.mem_filter.mp hlabel).1
  · intro x hx
    obtain ⟨label, hlabel, hxLabel⟩ := Finset.mem_biUnion.mp (hcover.2 hx)
    exact Finset.mem_biUnion.mpr
      ⟨label, Finset.mem_filter.mpr ⟨hlabel, ⟨x, hxLabel⟩⟩, hxLabel⟩

@[simp]
theorem mem_canonicalSeedResidualNeighbourhood
    {n x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel} :
    x ∈ canonicalSeedResidualNeighbourhood n a label ↔
      x ∈ canonicalNeighbourhood n a label ∧
        x ∈ canonicalSeedResidualPoints n a := by
  constructor
  · intro hx
    have hxData :
        x ∈ canonicalNeighbourhood n a label ∧
          x ∉ canonicalSeedCoveredPoints n a := by
      simpa [canonicalSeedResidualNeighbourhood,
        canonicalSeedCoveredPoints, residualNeighbourhood] using
        Finset.mem_sdiff.mp hx
    exact ⟨hxData.1, mem_canonicalSeedResidualPoints.mpr
      ⟨canonicalNeighbourhood_subset_unitInterval n a label hxData.1,
        hxData.2⟩⟩
  · rintro ⟨hxLabel, hxResidual⟩
    have hxData := mem_canonicalSeedResidualPoints.mp hxResidual
    change x ∈ residualNeighbourhood (supportOneSeedLabels n a)
      (canonicalNeighbourhood n a) label
    exact Finset.mem_sdiff.mpr ⟨hxLabel, hxData.2⟩

/-- A seed label has empty residual neighbourhood after seed-covered points are
deleted. -/
theorem canonicalSeedResidualNeighbourhood_eq_empty_of_mem
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hseed : label ∈ supportOneSeedLabels n a) :
    canonicalSeedResidualNeighbourhood n a label = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    have hxData := Finset.mem_sdiff.mp hx
    exact hxData.2 (Finset.mem_biUnion.mpr ⟨label, hseed, hxData.1⟩)
  · simp

/-- The prime-multiplication image of an old represented label is represented
in the enlarged modulus. -/
theorem primeMultiplicationLabelMap_mem_canonicalLabels
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hlabel : label ∈ canonicalLabels n a) :
    primeMultiplicationLabelMap a p label ∈ canonicalLabels (p * n) a := by
  obtain ⟨x, hx, q, hq, rfl⟩ := mem_canonicalLabels.mp hlabel
  have hpx := mul_mem_unitInterval_mul hpPrime.pos hx
  have hqNew : q ∈ supportedPrimes (p * n) (p * x) := by
    rw [supportedPrimes_mul_prime hpPrime hn0 hx]
    exact hq
  have hnewLabel := pointLabel_mem_canonicalLabels (a := a) hpx hqNew
  simpa only [pointLabel_mul_prime hpPrime hx] using hnewLabel

/-- Compatibility specialization of represented-label transport to an active
prime. -/
theorem activePrimeLabelMap_mem_canonicalLabels
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hlabel : label ∈ canonicalLabels n a) :
    activePrimeLabelMap a p label ∈ canonicalLabels (p * n) a := by
  exact primeMultiplicationLabelMap_mem_canonicalLabels
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hlabel

/-- Incidence with a represented label is preserved and reflected by prime
multiplication on points and labels. -/
theorem mul_mem_canonicalNeighbourhood_primeMultiplicationLabelMap_iff
    {n p x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hlabel : label ∈ canonicalLabels n a)
    (hx : x ∈ unitInterval n) :
    p * x ∈ canonicalNeighbourhood (p * n) a
        (primeMultiplicationLabelMap a p label) ↔
      x ∈ canonicalNeighbourhood n a label := by
  obtain ⟨z, hz, q, hq, rfl⟩ := mem_canonicalLabels.mp hlabel
  have hpz := mul_mem_unitInterval_mul hpPrime.pos hz
  have hqNew : q ∈ supportedPrimes (p * n) (p * z) := by
    rw [supportedPrimes_mul_prime hpPrime hn0 hz]
    exact hq
  have hqFactors : q ∈ n.primeFactors := (mem_supportedPrimes.mp hq).1
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqFactors
  have holdLabel := pointLabel_mem_canonicalLabels (a := a) hz hq
  have hnewLabel := pointLabel_mem_canonicalLabels (a := a) hpz hqNew
  rw [← pointLabel_mul_prime hpPrime hz]
  constructor
  · intro hpxLabel
    have hnewData :=
      (mem_canonicalNeighbourhood_iff_pointLabel_eq hnewLabel).mp hpxLabel
    have hlabels : pointLabel a q (p * x) = pointLabel a q (p * z) :=
      hnewData.2
    exact (mem_canonicalNeighbourhood_iff_pointLabel_eq holdLabel).mpr
      ⟨hx, (pointLabel_mul_prime_eq_iff hpPrime hqPrime hx hz).mp hlabels⟩
  · intro hxLabel
    have holdData :=
      (mem_canonicalNeighbourhood_iff_pointLabel_eq holdLabel).mp hxLabel
    have hlabels : pointLabel a q (p * x) = pointLabel a q (p * z) :=
      (pointLabel_mul_prime_eq_iff hpPrime hqPrime hx hz).mpr holdData.2
    exact (mem_canonicalNeighbourhood_iff_pointLabel_eq hnewLabel).mpr
      ⟨mul_mem_unitInterval_mul hpPrime.pos hx, hlabels⟩

/-- Compatibility specialization of represented-neighbourhood transport to
an active prime. -/
theorem mul_mem_canonicalNeighbourhood_activePrimeLabelMap_iff
    {n p x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hlabel : label ∈ canonicalLabels n a)
    (hx : x ∈ unitInterval n) :
    p * x ∈ canonicalNeighbourhood (p * n) a
        (activePrimeLabelMap a p label) ↔
      x ∈ canonicalNeighbourhood n a label := by
  exact mul_mem_canonicalNeighbourhood_primeMultiplicationLabelMap_iff
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hlabel hx

/-- The residual neighbourhood of an old represented label maps exactly to
the enlarged residual neighbourhood of its prime-multiplication label. -/
theorem canonicalSeedResidualNeighbourhood_primeMultiplicationLabelMap_eq_image
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p)
    (hlabel : label ∈ canonicalLabels n a) :
    canonicalSeedResidualNeighbourhood (p * n) a
        (primeMultiplicationLabelMap a p label) =
      (canonicalSeedResidualNeighbourhood n a label).image
        (fun x ↦ p * x) := by
  ext y
  constructor
  · intro hy
    have hyData := mem_canonicalSeedResidualNeighbourhood.mp hy
    have hyImage :
        y ∈ (canonicalSeedResidualPoints n a).image (fun x ↦ p * x) := by
      rw [← canonicalSeedResidualPoints_mul_prime_eq_image
        hpPrime hn0 hdepth]
      exact hyData.2
    obtain ⟨x, hxResidual, rfl⟩ := Finset.mem_image.mp hyImage
    have hxData := mem_canonicalSeedResidualPoints.mp hxResidual
    have hxLabel :=
      (mul_mem_canonicalNeighbourhood_primeMultiplicationLabelMap_iff
        hpPrime hn0 hlabel hxData.1).mp hyData.1
    exact Finset.mem_image.mpr
      ⟨x, mem_canonicalSeedResidualNeighbourhood.mpr
        ⟨hxLabel, hxResidual⟩, rfl⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hxData := mem_canonicalSeedResidualNeighbourhood.mp hx
    have hpxLabel :=
      (mul_mem_canonicalNeighbourhood_primeMultiplicationLabelMap_iff
        hpPrime hn0 hlabel
          (mem_canonicalSeedResidualPoints.mp hxData.2).1).mpr hxData.1
    have hpxResidual :
        p * x ∈ canonicalSeedResidualPoints (p * n) a := by
      rw [canonicalSeedResidualPoints_mul_prime_eq_image hpPrime hn0 hdepth]
      exact Finset.mem_image.mpr ⟨x, hxData.2, rfl⟩
    exact mem_canonicalSeedResidualNeighbourhood.mpr
      ⟨hpxLabel, hpxResidual⟩

/-- Compatibility specialization of residual-neighbourhood transport to an
active prime. -/
theorem canonicalSeedResidualNeighbourhood_activePrimeLabelMap_eq_image
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    (hlabel : label ∈ canonicalLabels n a) :
    canonicalSeedResidualNeighbourhood (p * n) a
        (activePrimeLabelMap a p label) =
      (canonicalSeedResidualNeighbourhood n a label).image
        (fun x ↦ p * x) := by
  exact canonicalSeedResidualNeighbourhood_primeMultiplicationLabelMap_eq_image
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth hlabel

/-- Every nonempty enlarged residual neighbourhood has an old represented
label whose prime-multiplication image produces that neighbourhood. -/
theorem exists_primeMultiplicationLabelMap_eq_of_residualNeighbourhood_nonempty
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p)
    (hlabel : label ∈ canonicalLabels (p * n) a)
    (hne : (canonicalSeedResidualNeighbourhood (p * n) a label).Nonempty) :
    ∃ oldLabel ∈ canonicalLabels n a \ supportOneSeedLabels n a,
      primeMultiplicationLabelMap a p oldLabel = label ∧
        canonicalSeedResidualNeighbourhood (p * n) a label =
          (canonicalSeedResidualNeighbourhood n a oldLabel).image
            (fun x ↦ p * x) := by
  obtain ⟨y, hy⟩ := hne
  have hyData := mem_canonicalSeedResidualNeighbourhood.mp hy
  have hyImage :
      y ∈ (canonicalSeedResidualPoints n a).image (fun x ↦ p * x) := by
    rw [← canonicalSeedResidualPoints_mul_prime_eq_image hpPrime hn0 hdepth]
    exact hyData.2
  obtain ⟨x, hxResidual, rfl⟩ := Finset.mem_image.mp hyImage
  have hxData := mem_canonicalSeedResidualPoints.mp hxResidual
  have hqNew :=
    labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood hlabel hyData.1
  have hqOld : label.prime ∈ supportedPrimes n x := by
    rw [← supportedPrimes_mul_prime hpPrime hn0 hxData.1]
    exact hqNew
  let oldLabel := pointLabel a label.prime x
  have hOldLabel : oldLabel ∈ canonicalLabels n a :=
    pointLabel_mem_canonicalLabels hxData.1 hqOld
  have hOldNotSeed : oldLabel ∉ supportOneSeedLabels n a := by
    intro hseed
    apply hxData.2
    exact Finset.mem_biUnion.mpr
      ⟨oldLabel, hseed, point_mem_canonicalNeighbourhood hxData.1⟩
  have hmap : primeMultiplicationLabelMap a p oldLabel = label := by
    calc
      primeMultiplicationLabelMap a p oldLabel =
          pointLabel a label.prime (p * x) := by
        simpa [oldLabel] using
          (pointLabel_mul_prime (a := a) hpPrime hxData.1).symm
      _ = label :=
        pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hyData.1
  refine ⟨oldLabel, Finset.mem_sdiff.mpr ⟨hOldLabel, hOldNotSeed⟩,
    hmap, ?_⟩
  rw [← hmap]
  exact canonicalSeedResidualNeighbourhood_primeMultiplicationLabelMap_eq_image
    hpPrime hn0 hdepth hOldLabel

/-- Compatibility specialization of nonempty-neighbourhood representation to
an active prime. -/
theorem exists_activePrimeLabelMap_eq_of_residualNeighbourhood_nonempty
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    (hlabel : label ∈ canonicalLabels (p * n) a)
    (hne : (canonicalSeedResidualNeighbourhood (p * n) a label).Nonempty) :
    ∃ oldLabel ∈ canonicalLabels n a \ supportOneSeedLabels n a,
      activePrimeLabelMap a p oldLabel = label ∧
        canonicalSeedResidualNeighbourhood (p * n) a label =
          (canonicalSeedResidualNeighbourhood n a oldLabel).image
            (fun x ↦ p * x) := by
  exact exists_primeMultiplicationLabelMap_eq_of_residualNeighbourhood_nonempty
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth hlabel hne

/-- A represented old label with a nonempty residual neighbourhood maps to an
available enlarged residual label under prime multiplication. -/
theorem primeMultiplicationLabelMap_mem_canonicalSeedResidualLabels_of_nonempty
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p)
    (hlabel : label ∈ canonicalLabels n a)
    (hne : (canonicalSeedResidualNeighbourhood n a label).Nonempty) :
    primeMultiplicationLabelMap a p label ∈
      canonicalSeedResidualLabels (p * n) a := by
  refine Finset.mem_sdiff.mpr
    ⟨primeMultiplicationLabelMap_mem_canonicalLabels hpPrime hn0 hlabel, ?_⟩
  intro hseed
  obtain ⟨x, hx⟩ := hne
  have hmap :=
    canonicalSeedResidualNeighbourhood_primeMultiplicationLabelMap_eq_image
      hpPrime hn0 hdepth hlabel
  have hpx :
      p * x ∈ canonicalSeedResidualNeighbourhood (p * n) a
        (primeMultiplicationLabelMap a p label) := by
    rw [hmap]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hempty :=
    canonicalSeedResidualNeighbourhood_eq_empty_of_mem hseed
  have hnot :
      p * x ∉ canonicalSeedResidualNeighbourhood (p * n) a
        (primeMultiplicationLabelMap a p label) := by
    rw [hempty]
    simp
  exact hnot hpx

/-- Compatibility specialization of residual-label availability to an active
prime. -/
theorem activePrimeLabelMap_mem_canonicalSeedResidualLabels_of_nonempty
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    (hlabel : label ∈ canonicalLabels n a)
    (hne : (canonicalSeedResidualNeighbourhood n a label).Nonempty) :
    activePrimeLabelMap a p label ∈ canonicalSeedResidualLabels (p * n) a := by
  exact primeMultiplicationLabelMap_mem_canonicalSeedResidualLabels_of_nonempty
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth hlabel hne

/-- Mapping the nonempty labels in an old residual cover by prime
multiplication produces an enlarged residual cover with no larger cardinality. -/
theorem exists_primeMultiplication_residualLabelCover_card_le
    {n p : ℕ} {a : ℕ → ℕ} {selected : Finset CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p)
    (hcover : IsLabelCover (canonicalSeedResidualLabels n a)
      (canonicalSeedResidualNeighbourhood n a) selected) :
    ∃ newSelected : Finset CanonicalBlockLabel,
      IsLabelCover (canonicalSeedResidualLabels (p * n) a)
          (canonicalSeedResidualNeighbourhood (p * n) a) newSelected ∧
        newSelected.card ≤ selected.card := by
  let selectedNonempty := selected.filter fun label ↦
    (canonicalSeedResidualNeighbourhood n a label).Nonempty
  let newSelected := selectedNonempty.image (primeMultiplicationLabelMap a p)
  refine ⟨newSelected, ?_, ?_⟩
  · constructor
    · intro newLabel hnewLabel
      obtain ⟨oldLabel, holdSelected, rfl⟩ := Finset.mem_image.mp hnewLabel
      have holdData := Finset.mem_filter.mp holdSelected
      have holdAvailable := hcover.1 holdData.1
      exact primeMultiplicationLabelMap_mem_canonicalSeedResidualLabels_of_nonempty
        hpPrime hn0 hdepth (Finset.mem_sdiff.mp holdAvailable).1 holdData.2
    · intro y hy
      obtain ⟨newLabel, hnewAvailable, hyLabel⟩ :=
        Finset.mem_biUnion.mp hy
      have hnewLabel := (Finset.mem_sdiff.mp hnewAvailable).1
      obtain ⟨oldLabel, holdAvailable, _, hneighbourhood⟩ :=
        exists_primeMultiplicationLabelMap_eq_of_residualNeighbourhood_nonempty
          hpPrime hn0 hdepth hnewLabel ⟨y, hyLabel⟩
      rw [hneighbourhood] at hyLabel
      obtain ⟨x, hxOldLabel, rfl⟩ := Finset.mem_image.mp hyLabel
      have hxOldFamily :
          x ∈ (canonicalSeedResidualLabels n a).biUnion
            (canonicalSeedResidualNeighbourhood n a) :=
        Finset.mem_biUnion.mpr ⟨oldLabel, holdAvailable, hxOldLabel⟩
      obtain ⟨selectedLabel, hselectedLabel, hxSelectedLabel⟩ :=
        Finset.mem_biUnion.mp (hcover.2 hxOldFamily)
      have hselectedAvailable := hcover.1 hselectedLabel
      have hselectedCanonical :=
        (Finset.mem_sdiff.mp hselectedAvailable).1
      have hselectedNonempty : selectedLabel ∈ selectedNonempty :=
        Finset.mem_filter.mpr
          ⟨hselectedLabel, ⟨x, hxSelectedLabel⟩⟩
      have hpxSelected :
          p * x ∈ canonicalSeedResidualNeighbourhood (p * n) a
            (primeMultiplicationLabelMap a p selectedLabel) := by
        rw [canonicalSeedResidualNeighbourhood_primeMultiplicationLabelMap_eq_image
          hpPrime hn0 hdepth hselectedCanonical]
        exact Finset.mem_image.mpr ⟨x, hxSelectedLabel, rfl⟩
      exact Finset.mem_biUnion.mpr
        ⟨primeMultiplicationLabelMap a p selectedLabel,
          Finset.mem_image.mpr ⟨selectedLabel, hselectedNonempty, rfl⟩,
          hpxSelected⟩
  · have hselectedNonemptySubset : selectedNonempty ⊆ selected := by
      intro label hlabel
      exact (Finset.mem_filter.mp hlabel).1
    calc
      newSelected.card ≤ selectedNonempty.card := Finset.card_image_le
      _ ≤ selected.card :=
        Finset.card_le_card hselectedNonemptySubset

/-- Compatibility specialization of forward residual-cover transport to an
active prime. -/
theorem exists_activePrime_residualLabelCover_card_le
    {n p : ℕ} {a : ℕ → ℕ} {selected : Finset CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    (hcover : IsLabelCover (canonicalSeedResidualLabels n a)
      (canonicalSeedResidualNeighbourhood n a) selected) :
    ∃ newSelected : Finset CanonicalBlockLabel,
      IsLabelCover (canonicalSeedResidualLabels (p * n) a)
          (canonicalSeedResidualNeighbourhood (p * n) a) newSelected ∧
        newSelected.card ≤ selected.card := by
  exact exists_primeMultiplication_residualLabelCover_card_le
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth hcover

/-- Pulling an enlarged residual cover back through prime-multiplication
neighbourhood representatives produces an old cover with no larger
cardinality. -/
theorem exists_residualLabelCover_card_le_of_primeMultiplication
    {n p : ℕ} {a : ℕ → ℕ} {selected : Finset CanonicalBlockLabel}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p)
    (hcover : IsLabelCover (canonicalSeedResidualLabels (p * n) a)
      (canonicalSeedResidualNeighbourhood (p * n) a) selected) :
    ∃ oldSelected : Finset CanonicalBlockLabel,
      IsLabelCover (canonicalSeedResidualLabels n a)
          (canonicalSeedResidualNeighbourhood n a) oldSelected ∧
        oldSelected.card ≤ selected.card := by
  let selectedNonempty := selected.filter fun label ↦
    (canonicalSeedResidualNeighbourhood (p * n) a label).Nonempty
  have hcoverNonempty :
      IsLabelCover (canonicalSeedResidualLabels (p * n) a)
        (canonicalSeedResidualNeighbourhood (p * n) a) selectedNonempty := by
    simpa [selectedNonempty] using isLabelCover_filter_nonempty hcover
  let transportedOldNeighbourhood : CanonicalBlockLabel → Finset ℕ :=
    fun label ↦ (canonicalSeedResidualNeighbourhood n a label).image
      (fun x ↦ p * x)
  let selectedBlocks := selectedNonempty.image
    (canonicalSeedResidualNeighbourhood (p * n) a)
  have hsurj :
      (canonicalSeedResidualLabels n a : Set CanonicalBlockLabel).SurjOn
        transportedOldNeighbourhood (selectedBlocks : Set (Finset ℕ)) := by
    intro block hblock
    have hblockMem : block ∈ selectedBlocks := by simpa using hblock
    obtain ⟨newLabel, hnewSelected, hnewBlock⟩ :=
      Finset.mem_image.mp hblockMem
    have hnewSelectedData := Finset.mem_filter.mp hnewSelected
    have hnewAvailable := hcover.1 hnewSelectedData.1
    obtain ⟨oldLabel, holdAvailable, _, hneighbourhood⟩ :=
      exists_primeMultiplicationLabelMap_eq_of_residualNeighbourhood_nonempty
        hpPrime hn0 hdepth (Finset.mem_sdiff.mp hnewAvailable).1
          hnewSelectedData.2
    refine ⟨oldLabel, ?_, ?_⟩
    · change oldLabel ∈ canonicalSeedResidualLabels n a
      exact holdAvailable
    exact hneighbourhood.symm.trans hnewBlock
  obtain ⟨oldSelected, holdSelected, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn
      (f := transportedOldNeighbourhood)
      (canonicalSeedResidualLabels n a : Set CanonicalBlockLabel)
      selectedBlocks hsurj
  have holdCover :
      IsLabelCover (canonicalSeedResidualLabels n a)
        (canonicalSeedResidualNeighbourhood n a) oldSelected := by
    constructor
    · simpa using holdSelected
    · intro x hx
      obtain ⟨oldLabel, holdAvailable, hxOldLabel⟩ :=
        Finset.mem_biUnion.mp hx
      have holdCanonical := (Finset.mem_sdiff.mp holdAvailable).1
      have hmapAvailable :=
        primeMultiplicationLabelMap_mem_canonicalSeedResidualLabels_of_nonempty
          hpPrime hn0 hdepth holdCanonical ⟨x, hxOldLabel⟩
      have hpxMap :
          p * x ∈ canonicalSeedResidualNeighbourhood (p * n) a
            (primeMultiplicationLabelMap a p oldLabel) := by
        rw [canonicalSeedResidualNeighbourhood_primeMultiplicationLabelMap_eq_image
          hpPrime hn0 hdepth holdCanonical]
        exact Finset.mem_image.mpr ⟨x, hxOldLabel, rfl⟩
      have hpxFamily :
          p * x ∈ (canonicalSeedResidualLabels (p * n) a).biUnion
            (canonicalSeedResidualNeighbourhood (p * n) a) :=
        Finset.mem_biUnion.mpr
          ⟨primeMultiplicationLabelMap a p oldLabel, hmapAvailable, hpxMap⟩
      obtain ⟨newLabel, hnewSelected, hpxNewLabel⟩ :=
        Finset.mem_biUnion.mp (hcoverNonempty.2 hpxFamily)
      have hblockMem :
          canonicalSeedResidualNeighbourhood (p * n) a newLabel ∈
            selectedBlocks :=
        Finset.mem_image.mpr ⟨newLabel, hnewSelected, rfl⟩
      have hblockOld :
          canonicalSeedResidualNeighbourhood (p * n) a newLabel ∈
            oldSelected.image transportedOldNeighbourhood := by
        rw [himage]
        exact hblockMem
      obtain ⟨oldSelectedLabel, holdSelectedLabel, hblock⟩ :=
        Finset.mem_image.mp hblockOld
      have hpxTransported :
          p * x ∈ transportedOldNeighbourhood oldSelectedLabel := by
        rw [hblock]
        exact hpxNewLabel
      change p * x ∈
        (canonicalSeedResidualNeighbourhood n a oldSelectedLabel).image
          (fun y ↦ p * y) at hpxTransported
      obtain ⟨y, hyOldLabel, hmul⟩ :=
        Finset.mem_image.mp hpxTransported
      have hyx : y = x := Nat.mul_left_cancel hpPrime.pos hmul
      exact Finset.mem_biUnion.mpr
        ⟨oldSelectedLabel, holdSelectedLabel, by simpa [hyx] using hyOldLabel⟩
  have hselectedNonemptySubset : selectedNonempty ⊆ selected := by
    intro label hlabel
    exact (Finset.mem_filter.mp hlabel).1
  have holdCard : oldSelected.card = selectedBlocks.card := by
    calc
      oldSelected.card =
          (oldSelected.image transportedOldNeighbourhood).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ = selectedBlocks.card := congrArg Finset.card himage
  refine ⟨oldSelected, holdCover, ?_⟩
  calc
    oldSelected.card = selectedBlocks.card := holdCard
    _ ≤ selectedNonempty.card := Finset.card_image_le
    _ ≤ selected.card := Finset.card_le_card hselectedNonemptySubset

/-- Compatibility specialization of reverse residual-cover transport to an
active prime. -/
theorem exists_residualLabelCover_card_le_of_activePrime
    {n p : ℕ} {a : ℕ → ℕ} {selected : Finset CanonicalBlockLabel}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    (hcover : IsLabelCover (canonicalSeedResidualLabels (p * n) a)
      (canonicalSeedResidualNeighbourhood (p * n) a) selected) :
    ∃ oldSelected : Finset CanonicalBlockLabel,
      IsLabelCover (canonicalSeedResidualLabels n a)
          (canonicalSeedResidualNeighbourhood n a) oldSelected ∧
        oldSelected.card ≤ selected.card := by
  exact exists_residualLabelCover_card_le_of_primeMultiplication
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth hcover

/-- Multiplication by any prime at stable depth leaves the labelled residual
cover number unchanged. -/
theorem canonicalSeedResidualLabelCoverNumber_mul_prime_eq
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    labelCoverNumber (canonicalSeedResidualLabels (p * n) a)
        (canonicalSeedResidualNeighbourhood (p * n) a) =
      labelCoverNumber (canonicalSeedResidualLabels n a)
        (canonicalSeedResidualNeighbourhood n a) := by
  apply le_antisymm
  · obtain ⟨oldSelected, holdCover, holdCard⟩ :=
      labelCoverNumber_attained (canonicalSeedResidualLabels n a)
        (canonicalSeedResidualNeighbourhood n a)
    obtain ⟨newSelected, hnewCover, hcardLe⟩ :=
      exists_primeMultiplication_residualLabelCover_card_le
        hpPrime hn0 hdepth holdCover
    calc
      labelCoverNumber (canonicalSeedResidualLabels (p * n) a)
          (canonicalSeedResidualNeighbourhood (p * n) a) ≤
          newSelected.card :=
        labelCoverNumber_le_card hnewCover
      _ ≤ oldSelected.card := hcardLe
      _ = labelCoverNumber (canonicalSeedResidualLabels n a)
          (canonicalSeedResidualNeighbourhood n a) := holdCard
  · obtain ⟨newSelected, hnewCover, hnewCard⟩ :=
      labelCoverNumber_attained (canonicalSeedResidualLabels (p * n) a)
        (canonicalSeedResidualNeighbourhood (p * n) a)
    obtain ⟨oldSelected, holdCover, hcardLe⟩ :=
      exists_residualLabelCover_card_le_of_primeMultiplication
        hpPrime hn0 hdepth hnewCover
    calc
      labelCoverNumber (canonicalSeedResidualLabels n a)
          (canonicalSeedResidualNeighbourhood n a) ≤
          oldSelected.card :=
        labelCoverNumber_le_card holdCover
      _ ≤ newSelected.card := hcardLe
      _ = labelCoverNumber (canonicalSeedResidualLabels (p * n) a)
          (canonicalSeedResidualNeighbourhood (p * n) a) := hnewCard

/-- Compatibility specialization of residual-cover-number invariance to an
active prime. -/
theorem canonicalSeedResidualLabelCoverNumber_mul_eq
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    labelCoverNumber (canonicalSeedResidualLabels (p * n) a)
        (canonicalSeedResidualNeighbourhood (p * n) a) =
      labelCoverNumber (canonicalSeedResidualLabels n a)
        (canonicalSeedResidualNeighbourhood n a) := by
  exact canonicalSeedResidualLabelCoverNumber_mul_prime_eq
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth

/-- Adjoining one copy of an active prime at or above its stable depth adds
exactly the last stable layer to the closed support-one seed count. -/
theorem seedCountFormula_mul_activePrime
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    seedCountFormula (p * n) a =
      seedCountFormula n a + (p - 1) * p ^ a p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hprimeFactors : (p * n).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul hpPrime.ne_zero hn0, hpPrime.primeFactors]
    simp [hp]
  let newTerm := fun q ↦
    (q - 1) * ∑ j ∈ Finset.range ((p * n).factorization q),
      q ^ min (a q) j
  let oldTerm := fun q ↦
    (q - 1) * ∑ j ∈ Finset.range (n.factorization q),
      q ^ min (a q) j
  rw [seedCountFormula, seedCountFormula, hprimeFactors]
  change (∑ q ∈ n.primeFactors, newTerm q) =
    (∑ q ∈ n.primeFactors, oldTerm q) + (p - 1) * p ^ a p
  have herase :
      (∑ q ∈ n.primeFactors.erase p, newTerm q) =
        ∑ q ∈ n.primeFactors.erase p, oldTerm q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
    have hfactor : (p * n).factorization q = n.factorization q := by
      rw [Nat.factorization_mul hpPrime.ne_zero hn0, Finsupp.add_apply]
      simp [hpPrime.factorization, hqp]
    simp only [newTerm, oldTerm]
    rw [hfactor]
  have hpTerm :
      newTerm p = oldTerm p + (p - 1) * p ^ a p := by
    simp only [newTerm, oldTerm]
    rw [factorization_mul_left_self_eq_succ_of_mem_primeFactors hp,
      Finset.sum_range_succ, min_eq_left hdepth, Nat.mul_add]
  calc
    (∑ q ∈ n.primeFactors, newTerm q) =
        (∑ q ∈ n.primeFactors.erase p, newTerm q) + newTerm p :=
      (Finset.sum_erase_add n.primeFactors newTerm hp).symm
    _ = (∑ q ∈ n.primeFactors.erase p, oldTerm q) +
        (oldTerm p + (p - 1) * p ^ a p) := by rw [herase, hpTerm]
    _ = ((∑ q ∈ n.primeFactors.erase p, oldTerm q) + oldTerm p) +
        (p - 1) * p ^ a p := by rw [Nat.add_assoc]
    _ = (∑ q ∈ n.primeFactors, oldTerm q) +
        (p - 1) * p ^ a p := by
      rw [Finset.sum_erase_add n.primeFactors oldTerm hp]

/-- Multiplication by any prime at stable depth adds one stable layer to the
closed support-one seed count.  When the prime is new, stable depth forces its
prescribed depth to be zero. -/
theorem seedCountFormula_mul_prime
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    seedCountFormula (p * n) a =
      seedCountFormula n a + (p - 1) * p ^ a p := by
  by_cases hpMem : p ∈ n.primeFactors
  · exact seedCountFormula_mul_activePrime hpMem hdepth
  · have hpNotDvd : ¬p ∣ n := by
      intro hpDvd
      exact hpMem (Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvd, hn0⟩)
    have hnFactor : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpNotDvd
    have ha : a p = 0 := by omega
    have hprimeFactors :
        (p * n).primeFactors = insert p n.primeFactors := by
      rw [Nat.primeFactors_mul hpPrime.ne_zero hn0, hpPrime.primeFactors]
      simp
    have hfactorP : (p * n).factorization p = 1 := by
      rw [factorization_mul_left_self_eq_succ_of_prime hpPrime hn0, hnFactor]
    let newTerm := fun q ↦
      (q - 1) * ∑ j ∈ Finset.range ((p * n).factorization q),
        q ^ min (a q) j
    let oldTerm := fun q ↦
      (q - 1) * ∑ j ∈ Finset.range (n.factorization q),
        q ^ min (a q) j
    rw [seedCountFormula, seedCountFormula, hprimeFactors]
    change (∑ q ∈ insert p n.primeFactors, newTerm q) =
      (∑ q ∈ n.primeFactors, oldTerm q) + (p - 1) * p ^ a p
    rw [Finset.sum_insert hpMem]
    have hrest :
        (∑ q ∈ n.primeFactors, newTerm q) =
          ∑ q ∈ n.primeFactors, oldTerm q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqp : q ≠ p := by
        intro hEq
        subst q
        exact hpMem hq
      have hfactor : (p * n).factorization q = n.factorization q := by
        rw [Nat.factorization_mul hpPrime.ne_zero hn0, Finsupp.add_apply]
        simp [hpPrime.factorization, hqp]
      simp only [newTerm, oldTerm]
      rw [hfactor]
    rw [hrest]
    simp [newTerm, hfactorP, ha, Nat.add_comm]

/-- The arithmetic seed residual is the extensional image of the represented
nonseed labels with their seed-deleted neighbourhoods. -/
theorem canonicalSeedResidual_eq_extensionalImage
    (n : ℕ) (a : ℕ → ℕ) :
    canonicalSeedResidual n a =
      extensionalImage (canonicalSeedResidualLabels n a)
        (canonicalSeedResidualNeighbourhood n a) := by
  change extensionalImage
      (canonicalLabels n a \ canonicalPrivateLabels n a)
        (residualNeighbourhood (canonicalPrivateLabels n a)
          (canonicalNeighbourhood n a)) =
    extensionalImage (canonicalSeedResidualLabels n a)
      (canonicalSeedResidualNeighbourhood n a)
  rw [canonicalPrivateLabels_eq_supportOneSeedLabels]
  rfl

/-- Multiplication by any prime at stable depth leaves the extensional
canonical seed-residual cover number unchanged. -/
theorem axisCover_canonicalSeedResidual_mul_prime_eq
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    axis_cover (canonicalSeedResidual (p * n) a) =
      axis_cover (canonicalSeedResidual n a) := by
  calc
    axis_cover (canonicalSeedResidual (p * n) a) =
        labelCoverNumber (canonicalSeedResidualLabels (p * n) a)
          (canonicalSeedResidualNeighbourhood (p * n) a) := by
      rw [canonicalSeedResidual_eq_extensionalImage]
      simpa [axis_cover] using
        (labelCoverNumber_eq_tau_extensionalImage
          (canonicalSeedResidualLabels (p * n) a)
          (canonicalSeedResidualNeighbourhood (p * n) a)).symm
    _ = labelCoverNumber (canonicalSeedResidualLabels n a)
        (canonicalSeedResidualNeighbourhood n a) :=
      canonicalSeedResidualLabelCoverNumber_mul_prime_eq hpPrime hn0 hdepth
    _ = axis_cover (canonicalSeedResidual n a) := by
      rw [canonicalSeedResidual_eq_extensionalImage]
      simpa [axis_cover] using
        labelCoverNumber_eq_tau_extensionalImage
          (canonicalSeedResidualLabels n a)
          (canonicalSeedResidualNeighbourhood n a)

/-- Compatibility specialization of seed-residual cover invariance to an
active prime. -/
theorem axisCover_canonicalSeedResidual_mul_eq
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    axis_cover (canonicalSeedResidual (p * n) a) =
      axis_cover (canonicalSeedResidual n a) := by
  exact axisCover_canonicalSeedResidual_mul_prime_eq
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth

/-- Above the active depth, adjoining one copy of an active prime increases
the canonical extensional cover number by the last stable seed layer. -/
theorem axisCover_canonicalExtensionalFamily_mul_eq
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    axis_cover (canonicalExtensionalFamily (p * n) a) =
      axis_cover (canonicalExtensionalFamily n a) +
        (p - 1) * p ^ a p := by
  calc
    axis_cover (canonicalExtensionalFamily (p * n) a) =
        seedCountFormula (p * n) a +
          axis_cover (canonicalSeedResidual (p * n) a) :=
      axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual
        (p * n) a
    _ = (seedCountFormula n a + (p - 1) * p ^ a p) +
        axis_cover (canonicalSeedResidual n a) := by
      rw [seedCountFormula_mul_activePrime hp hdepth,
        axisCover_canonicalSeedResidual_mul_eq hp hdepth]
    _ = (seedCountFormula n a + axis_cover (canonicalSeedResidual n a)) +
        (p - 1) * p ^ a p := by omega
    _ = axis_cover (canonicalExtensionalFamily n a) +
        (p - 1) * p ^ a p := by
      rw [axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual]

/-- At stable depth, multiplication by any prime adds exactly one closed seed
layer to the canonical extensional cover number.  This includes the first
copy of a previously absent prime, where stable depth forces `a p = 0`. -/
theorem axisCover_canonicalExtensionalFamily_mul_prime_eq
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    axis_cover (canonicalExtensionalFamily (p * n) a) =
      axis_cover (canonicalExtensionalFamily n a) +
        (p - 1) * p ^ a p := by
  calc
    axis_cover (canonicalExtensionalFamily (p * n) a) =
        seedCountFormula (p * n) a +
          axis_cover (canonicalSeedResidual (p * n) a) :=
      axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual
        (p * n) a
    _ = (seedCountFormula n a + (p - 1) * p ^ a p) +
        axis_cover (canonicalSeedResidual n a) := by
      rw [seedCountFormula_mul_prime hpPrime hn0 hdepth,
        axisCover_canonicalSeedResidual_mul_prime_eq hpPrime hn0 hdepth]
    _ = (seedCountFormula n a + axis_cover (canonicalSeedResidual n a)) +
        (p - 1) * p ^ a p := by omega
    _ = axis_cover (canonicalExtensionalFamily n a) +
        (p - 1) * p ^ a p := by
      rw [axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual]

/-- Inserting a previously absent prime of prescribed depth zero adds its
first inactive-axis contribution. -/
theorem axisCover_canonicalExtensionalFamily_mul_eq_of_prime_not_mem
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (_hpNot : p ∉ n.primeFactors) (ha : a p = 0) :
    axis_cover (canonicalExtensionalFamily (p * n) a) =
      axis_cover (canonicalExtensionalFamily n a) + (p - 1) := by
  simpa [ha] using
    (axisCover_canonicalExtensionalFamily_mul_prime_eq
      (n := n) (p := p) (a := a) hpPrime hn0 (by simp [ha]))

end ModularSchur.CanonicalBlocks
