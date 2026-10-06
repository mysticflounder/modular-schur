/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

module

public import ModularSchur.CanonicalBlocks

/-!
# Canonical block monotonicity

Increasing a canonical depth makes every represented congruence block finer.
This module projects fine labels to coarse labels and transfers covers along
that projection.  The result applies after restriction to any finite point
set, so in particular it controls every canonical prefix cover.
-/

@[expose] public section

namespace ModularSchur.CanonicalBlocks

open Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- Project a canonical label to the residue seen at a coarser depth vector. -/
def coarsenCanonicalLabel (a : ℕ → ℕ) (label : CanonicalBlockLabel) :
    CanonicalBlockLabel where
  prime := label.prime
  layer := label.layer
  residue := label.residue % label.prime ^ (a label.prime + label.layer + 1)

/-- Coarsening a point-generated label recovers the label generated at the
coarser depth. -/
theorem coarsenCanonicalLabel_pointLabel
    {a b : ℕ → ℕ} {p : ℕ} (hab : a p ≤ b p) (x : ℕ) :
    coarsenCanonicalLabel a (pointLabel b p x) = pointLabel a p x := by
  change
    ({ prime := p
       layer := x.factorization p
       residue := (x % p ^ (b p + x.factorization p + 1)) %
         p ^ (a p + x.factorization p + 1) } : CanonicalBlockLabel) =
      { prime := p
        layer := x.factorization p
        residue := x % p ^ (a p + x.factorization p + 1) }
  congr 1
  exact Nat.mod_mod_of_dvd x (pow_dvd_pow p (by omega))

/-- The prime stored by a represented label divides the canonical quotient. -/
theorem canonicalLabel_prime_mem_primeFactors
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a) :
    label.prime ∈ n.primeFactors := by
  obtain ⟨x, _, p, hp, hpoint⟩ := mem_canonicalLabels.mp hlabel
  rw [← hpoint]
  exact (mem_supportedPrimes.mp hp).1

/-- A represented fine label projects to an available coarse label. -/
theorem coarsenCanonicalLabel_mem_canonicalLabels
    {n : ℕ} {a b : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p ≤ b p)
    {label : CanonicalBlockLabel} (hlabel : label ∈ canonicalLabels n b) :
    coarsenCanonicalLabel a label ∈ canonicalLabels n a := by
  obtain ⟨x, hx, p, hp, rfl⟩ := mem_canonicalLabels.mp hlabel
  rw [coarsenCanonicalLabel_pointLabel
    (hab p (mem_supportedPrimes.mp hp).1)]
  exact pointLabel_mem_canonicalLabels hx hp

/-- A fine canonical neighbourhood is contained in its projected coarse
neighbourhood. -/
theorem canonicalNeighbourhood_subset_coarsened
    {n : ℕ} {a b : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hab : a label.prime ≤ b label.prime) :
    canonicalNeighbourhood n b label ⊆
      canonicalNeighbourhood n a (coarsenCanonicalLabel a label) := by
  intro x hx
  rw [mem_canonicalNeighbourhood] at hx ⊢
  refine ⟨hx.1, ?_⟩
  simp only [coarsenCanonicalLabel, labelModulus]
  have hdvd :
      label.prime ^ (a label.prime + label.layer + 1) ∣
        label.prime ^ (b label.prime + label.layer + 1) :=
    pow_dvd_pow label.prime (by omega)
  have hxeq :
      x % label.prime ^ (b label.prime + label.layer + 1) =
        label.residue := by
    simpa only [labelModulus] using hx.2
  calc
    x % label.prime ^ (a label.prime + label.layer + 1) =
        (x % label.prime ^ (b label.prime + label.layer + 1)) %
          label.prime ^ (a label.prime + label.layer + 1) :=
      (Nat.mod_mod_of_dvd x hdvd).symm
    _ = label.residue % label.prime ^ (a label.prime + label.layer + 1) := by
      rw [hxeq]

/-- The canonical block family after every block is restricted to `U`. -/
def canonicalRestrictedExtensionalFamily
    (n : ℕ) (a : ℕ → ℕ) (U : Finset ℕ) : Finset (Finset ℕ) :=
  extensionalImage (canonicalLabels n a) fun label ↦
    canonicalNeighbourhood n a label ∩ U

/-- The canonical family restricted to the prefix `[1, N]`. -/
def canonicalPrefixExtensionalFamily
    (n : ℕ) (a : ℕ → ℕ) (N : ℕ) : Finset (Finset ℕ) :=
  canonicalRestrictedExtensionalFamily n a (Finset.Ioc 0 N)

/-- Coordinatewise larger depths cannot lower a restricted canonical cover
number.  Only primes dividing `n` matter. -/
theorem axisCover_canonicalRestrictedExtensionalFamily_mono
    (n : ℕ) (U : Finset ℕ) {a b : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p ≤ b p) :
    axis_cover (canonicalRestrictedExtensionalFamily n a U) ≤
      axis_cover (canonicalRestrictedExtensionalFamily n b U) := by
  simp only [axis_cover, canonicalRestrictedExtensionalFamily]
  rw [← labelCoverNumber_eq_tau_extensionalImage,
    ← labelCoverNumber_eq_tau_extensionalImage]
  obtain ⟨selected, hselected, hcard⟩ :=
    labelCoverNumber_attained (canonicalLabels n b)
      (fun label ↦ canonicalNeighbourhood n b label ∩ U)
  let projected := selected.image (coarsenCanonicalLabel a)
  have hprojected :
      IsLabelCover (canonicalLabels n a)
        (fun label ↦ canonicalNeighbourhood n a label ∩ U) projected := by
    constructor
    · intro label hlabel
      obtain ⟨fineLabel, hfineSelected, rfl⟩ := Finset.mem_image.mp hlabel
      exact coarsenCanonicalLabel_mem_canonicalLabels hab
        (hselected.1 hfineSelected)
    · intro x hx
      rcases Finset.mem_biUnion.mp hx with
        ⟨coarseLabel, _, hxCoarseRestricted⟩
      have hxCoarse := (Finset.mem_inter.mp hxCoarseRestricted).1
      have hxU := (Finset.mem_inter.mp hxCoarseRestricted).2
      have hxUnit : x ∈ unitInterval n :=
        canonicalNeighbourhood_subset_unitInterval n a coarseLabel hxCoarse
      obtain ⟨fineLabel, hfineLabel, hxFine⟩ :=
        Finset.mem_biUnion.mp
          (unitInterval_subset_biUnion_canonicalLabels n b hxUnit)
      have hxFineRestricted :
          x ∈ (canonicalLabels n b).biUnion
            (fun label ↦ canonicalNeighbourhood n b label ∩ U) :=
        Finset.mem_biUnion.mpr ⟨fineLabel, hfineLabel,
          Finset.mem_inter.mpr ⟨hxFine, hxU⟩⟩
      rcases Finset.mem_biUnion.mp (hselected.2 hxFineRestricted) with
        ⟨selectedLabel, hselectedLabel, hxSelectedRestricted⟩
      have hxSelected := (Finset.mem_inter.mp hxSelectedRestricted).1
      have hxSelectedU := (Finset.mem_inter.mp hxSelectedRestricted).2
      have hselectedAvailable := hselected.1 hselectedLabel
      have hprime := canonicalLabel_prime_mem_primeFactors hselectedAvailable
      exact Finset.mem_biUnion.mpr
        ⟨coarsenCanonicalLabel a selectedLabel,
          Finset.mem_image.mpr ⟨selectedLabel, hselectedLabel, rfl⟩,
          Finset.mem_inter.mpr
            ⟨canonicalNeighbourhood_subset_coarsened
                (hab selectedLabel.prime hprime) hxSelected,
              hxSelectedU⟩⟩
  calc
    labelCoverNumber (canonicalLabels n a)
        (fun label ↦ canonicalNeighbourhood n a label ∩ U) ≤
      projected.card := labelCoverNumber_le_card hprojected
    _ ≤ selected.card := Finset.card_image_le
    _ = labelCoverNumber (canonicalLabels n b)
        (fun label ↦ canonicalNeighbourhood n b label ∩ U) := hcard

/-- Matching depth data on primes dividing `n` gives matching restricted cover
numbers. -/
theorem axisCover_canonicalRestrictedExtensionalFamily_congr
    (n : ℕ) (U : Finset ℕ) {a b : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p = b p) :
    axis_cover (canonicalRestrictedExtensionalFamily n a U) =
      axis_cover (canonicalRestrictedExtensionalFamily n b U) := by
  apply Nat.le_antisymm
  · exact axisCover_canonicalRestrictedExtensionalFamily_mono n U
      (fun p hp ↦ (hab p hp).le)
  · exact axisCover_canonicalRestrictedExtensionalFamily_mono n U
      (fun p hp ↦ (hab p hp).ge)

/-- Divisibility gives restricted canonical-cover monotonicity through natural
number factorization. -/
theorem axisCover_canonicalRestrictedExtensionalFamily_factorization_mono
    (n d d' : ℕ) (U : Finset ℕ) (hd0 : d ≠ 0) (hd'0 : d' ≠ 0)
    (hdd' : d ∣ d') :
    axis_cover
        (canonicalRestrictedExtensionalFamily n (fun p ↦ d.factorization p) U) ≤
      axis_cover
        (canonicalRestrictedExtensionalFamily n (fun p ↦ d'.factorization p) U) := by
  apply axisCover_canonicalRestrictedExtensionalFamily_mono
  intro p _
  exact Nat.factorization_le_factorization_of_dvd_right hdd' hd0 hd'0

/-- Restricting canonical blocks to their ambient interval changes nothing. -/
theorem canonicalRestrictedExtensionalFamily_unitInterval
    (n : ℕ) (a : ℕ → ℕ) :
    canonicalRestrictedExtensionalFamily n a (unitInterval n) =
      canonicalExtensionalFamily n a := by
  apply Finset.image_congr
  intro label _
  exact Finset.inter_eq_left.mpr
    (canonicalNeighbourhood_subset_unitInterval n a label)

/-- Coordinatewise larger depths cannot lower the terminal canonical cover
number. -/
theorem axisCover_canonicalExtensionalFamily_mono
    (n : ℕ) {a b : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p ≤ b p) :
    axis_cover (canonicalExtensionalFamily n a) ≤
      axis_cover (canonicalExtensionalFamily n b) := by
  have hmono := axisCover_canonicalRestrictedExtensionalFamily_mono
    n (unitInterval n) hab
  simpa only [canonicalRestrictedExtensionalFamily_unitInterval] using hmono

/-- Matching depth data on primes dividing `n` gives matching terminal cover
numbers. -/
theorem axisCover_canonicalExtensionalFamily_congr
    (n : ℕ) {a b : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p = b p) :
    axis_cover (canonicalExtensionalFamily n a) =
      axis_cover (canonicalExtensionalFamily n b) := by
  apply Nat.le_antisymm
  · exact axisCover_canonicalExtensionalFamily_mono n
      (fun p hp ↦ (hab p hp).le)
  · exact axisCover_canonicalExtensionalFamily_mono n
      (fun p hp ↦ (hab p hp).ge)

/-- Divisibility gives terminal canonical-cover monotonicity through natural
number factorization. -/
theorem axisCover_canonicalExtensionalFamily_factorization_mono
    (n d d' : ℕ) (hd0 : d ≠ 0) (hd'0 : d' ≠ 0) (hdd' : d ∣ d') :
    axis_cover (canonicalExtensionalFamily n (fun p ↦ d.factorization p)) ≤
      axis_cover
        (canonicalExtensionalFamily n (fun p ↦ d'.factorization p)) := by
  apply axisCover_canonicalExtensionalFamily_mono
  intro p _
  exact Nat.factorization_le_factorization_of_dvd_right hdd' hd0 hd'0

/-- Canonical prefix covers are monotone in the depth vector. -/
theorem axisCover_canonicalPrefixExtensionalFamily_mono
    (n N : ℕ) {a b : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p ≤ b p) :
    axis_cover (canonicalPrefixExtensionalFamily n a N) ≤
      axis_cover (canonicalPrefixExtensionalFamily n b N) := by
  exact axisCover_canonicalRestrictedExtensionalFamily_mono n (Finset.Ioc 0 N) hab

/-- A monotone intermediate depth has the same restricted cover number when
both endpoints do. -/
theorem axisCover_canonicalRestrictedExtensionalFamily_eq_of_between
    (n : ℕ) (U : Finset ℕ) {a b c : ℕ → ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p ≤ b p)
    (hbc : ∀ p ∈ n.primeFactors, b p ≤ c p)
    (hac : axis_cover (canonicalRestrictedExtensionalFamily n a U) =
      axis_cover (canonicalRestrictedExtensionalFamily n c U)) :
    axis_cover (canonicalRestrictedExtensionalFamily n b U) =
      axis_cover (canonicalRestrictedExtensionalFamily n a U) := by
  have habCover := axisCover_canonicalRestrictedExtensionalFamily_mono n U hab
  have hbcCover := axisCover_canonicalRestrictedExtensionalFamily_mono n U hbc
  omega

/-- Once a monotone cover number reaches a common upper bound, it stays there
at every larger depth where that bound remains valid. -/
theorem axisCover_canonicalRestrictedExtensionalFamily_eq_of_mono_of_upper
    (n : ℕ) (U : Finset ℕ) {a b : ℕ → ℕ} {K : ℕ}
    (hab : ∀ p ∈ n.primeFactors, a p ≤ b p)
    (ha : axis_cover (canonicalRestrictedExtensionalFamily n a U) = K)
    (hb : axis_cover (canonicalRestrictedExtensionalFamily n b U) ≤ K) :
    axis_cover (canonicalRestrictedExtensionalFamily n b U) = K := by
  have hmono := axisCover_canonicalRestrictedExtensionalFamily_mono n U hab
  omega

end ModularSchur.CanonicalBlocks
