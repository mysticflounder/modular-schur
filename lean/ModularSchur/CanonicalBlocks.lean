/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.AxisLabelledCover
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Arithmetic canonical blocks

This file supplies the natural-number label family consumed by
`AxisLabelledCover`.  A label records a prime axis, the valuation layer of a
point on that axis, and its residue at the stable canonical modulus.  Labels
are generated from actual point-axis incidences, so every stored label has a
nonempty neighbourhood.

The file also identifies private labels with points supported on exactly one
prime axis.  The separate `CanonicalSeedCount` module proves the closed
cardinality formula for that seed family.
-/

namespace ModularSchur.CanonicalBlocks

open Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- The ordered natural-number universe underlying a quotient of size `n`. -/
def unitInterval (n : ℕ) : Finset ℕ :=
  Finset.Ico 1 n

/-- An axis-labelled canonical block: prime, valuation layer, and residue. -/
structure CanonicalBlockLabel where
  prime : ℕ
  layer : ℕ
  residue : ℕ
  deriving DecidableEq, Repr

/-- The stable congruence modulus attached to a canonical block label. -/
def labelModulus (a : ℕ → ℕ) (label : CanonicalBlockLabel) : ℕ :=
  label.prime ^ (a label.prime + label.layer + 1)

/-- The label contributed by point `x` on prime axis `p`. -/
def pointLabel (a : ℕ → ℕ) (p x : ℕ) : CanonicalBlockLabel where
  prime := p
  layer := x.factorization p
  residue := x % p ^ (a p + x.factorization p + 1)

/-- Prime axes on which `x` has valuation below the exponent present in `n`. -/
def supportedPrimes (n x : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p ↦ x.factorization p < n.factorization p

/-- All canonical labels represented by a point of `[1,n)`. -/
def canonicalLabels (n : ℕ) (a : ℕ → ℕ) : Finset CanonicalBlockLabel :=
  (unitInterval n).biUnion fun x ↦
    (supportedPrimes n x).image fun p ↦ pointLabel a p x

/-- The point set of a represented canonical label. -/
def canonicalNeighbourhood (n : ℕ) (a : ℕ → ℕ)
    (label : CanonicalBlockLabel) : Finset ℕ :=
  (unitInterval n).filter fun x ↦ x % labelModulus a label = label.residue

@[simp]
theorem mem_unitInterval {n x : ℕ} :
    x ∈ unitInterval n ↔ 1 ≤ x ∧ x < n := by
  simp [unitInterval]

@[simp]
theorem mem_supportedPrimes {n x p : ℕ} :
    p ∈ supportedPrimes n x ↔
      p ∈ n.primeFactors ∧ x.factorization p < n.factorization p := by
  simp [supportedPrimes]

@[simp]
theorem mem_canonicalLabels {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel} :
    label ∈ canonicalLabels n a ↔
      ∃ x ∈ unitInterval n, ∃ p ∈ supportedPrimes n x,
        pointLabel a p x = label := by
  simp [canonicalLabels]

@[simp]
theorem mem_canonicalNeighbourhood {n x : ℕ} {a : ℕ → ℕ}
    {label : CanonicalBlockLabel} :
    x ∈ canonicalNeighbourhood n a label ↔
      x ∈ unitInterval n ∧ x % labelModulus a label = label.residue := by
  simp [canonicalNeighbourhood]

/-- A point belongs to the canonical block label that it generates. -/
theorem point_mem_canonicalNeighbourhood {n p x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ unitInterval n) :
    x ∈ canonicalNeighbourhood n a (pointLabel a p x) := by
  exact mem_canonicalNeighbourhood.mpr ⟨hx, rfl⟩

/-- A supported point-axis incidence generates an available label. -/
theorem pointLabel_mem_canonicalLabels {n p x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ unitInterval n) (hp : p ∈ supportedPrimes n x) :
    pointLabel a p x ∈ canonicalLabels n a := by
  exact Finset.mem_biUnion.mpr
    ⟨x, hx, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

/-- A point's labels on distinct prime axes remain distinct. -/
theorem pointLabel_injective (a : ℕ → ℕ) (x : ℕ) :
    Function.Injective fun p ↦ pointLabel a p x := by
  intro p q hEq
  simpa [pointLabel] using congrArg CanonicalBlockLabel.prime hEq

/-- Every represented canonical label has a nonempty neighbourhood. -/
theorem canonicalNeighbourhood_nonempty_of_mem {n : ℕ} {a : ℕ → ℕ}
    {label : CanonicalBlockLabel} (hlabel : label ∈ canonicalLabels n a) :
    (canonicalNeighbourhood n a label).Nonempty := by
  obtain ⟨x, hx, p, hp, rfl⟩ := mem_canonicalLabels.mp hlabel
  exact ⟨x, point_mem_canonicalNeighbourhood hx⟩

/-- Congruence at a represented canonical modulus preserves its valuation layer. -/
theorem factorization_eq_layer_of_mem_canonicalNeighbourhood
    {n x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a)
    (hx : x ∈ canonicalNeighbourhood n a label) :
    x.factorization label.prime = label.layer := by
  obtain ⟨y, hy, p, hpSupported, rfl⟩ := mem_canonicalLabels.mp hlabel
  change x.factorization p = y.factorization p
  have hxUnit := (mem_canonicalNeighbourhood.mp hx).1
  have hpFactors := (mem_supportedPrimes.mp hpSupported).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
  have hx0 : x ≠ 0 := by
    have := (mem_unitInterval.mp hxUnit).1
    omega
  have hy0 : y ≠ 0 := by
    have := (mem_unitInterval.mp hy).1
    omega
  have hmod : x ≡ y [MOD p ^ (a p + y.factorization p + 1)] := by
    simpa [Nat.ModEq, labelModulus, pointLabel] using
      (mem_canonicalNeighbourhood.mp hx).2
  have hpowDvd :
      p ^ y.factorization p ∣ p ^ (a p + y.factorization p + 1) :=
    pow_dvd_pow p (by omega)
  have hpowSuccDvd :
      p ^ (y.factorization p + 1) ∣ p ^ (a p + y.factorization p + 1) :=
    pow_dvd_pow p (by omega)
  have hyDvd : p ^ y.factorization p ∣ y :=
    (hpPrime.pow_dvd_iff_le_factorization hy0).2 le_rfl
  have hyNotDvd : ¬p ^ (y.factorization p + 1) ∣ y := by
    intro hdiv
    have := (hpPrime.pow_dvd_iff_le_factorization hy0).1 hdiv
    omega
  have hxDvd : p ^ y.factorization p ∣ x :=
    (hmod.dvd_iff hpowDvd).2 hyDvd
  have hxNotDvd : ¬p ^ (y.factorization p + 1) ∣ x := by
    intro hdiv
    exact hyNotDvd ((hmod.dvd_iff hpowSuccDvd).1 hdiv)
  have hlower : y.factorization p ≤ x.factorization p :=
    (hpPrime.pow_dvd_iff_le_factorization hx0).1 hxDvd
  have hupper : ¬y.factorization p + 1 ≤ x.factorization p := by
    intro hle
    exact hxNotDvd ((hpPrime.pow_dvd_iff_le_factorization hx0).2 hle)
  omega

/-- Membership in a represented block recovers the point's label on that axis. -/
theorem pointLabel_eq_of_mem_canonicalNeighbourhood
    {n x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a)
    (hx : x ∈ canonicalNeighbourhood n a label) :
    pointLabel a label.prime x = label := by
  have hlayer := factorization_eq_layer_of_mem_canonicalNeighbourhood hlabel hx
  have hresidue := (mem_canonicalNeighbourhood.mp hx).2
  cases label with
  | mk p t r =>
      change x.factorization p = t at hlayer
      change x % p ^ (a p + t + 1) = r at hresidue
      simp [pointLabel, hlayer, hresidue]

/-- On represented labels, block membership is equality with the point's axis label. -/
theorem mem_canonicalNeighbourhood_iff_pointLabel_eq
    {n x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a) :
    x ∈ canonicalNeighbourhood n a label ↔
      x ∈ unitInterval n ∧ pointLabel a label.prime x = label := by
  constructor
  · intro hx
    exact ⟨(mem_canonicalNeighbourhood.mp hx).1,
      pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hx⟩
  · rintro ⟨hx, hEq⟩
    rw [← hEq]
    exact point_mem_canonicalNeighbourhood hx

/-- The axis of every canonical block containing `x` is supported at `x`. -/
theorem labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood
    {n x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a)
    (hx : x ∈ canonicalNeighbourhood n a label) :
    label.prime ∈ supportedPrimes n x := by
  have hxLayer := factorization_eq_layer_of_mem_canonicalNeighbourhood hlabel hx
  obtain ⟨y, _, p, hpSupported, rfl⟩ := mem_canonicalLabels.mp hlabel
  change p ∈ supportedPrimes n x
  change x.factorization p = y.factorization p at hxLayer
  have hpData := mem_supportedPrimes.mp hpSupported
  exact mem_supportedPrimes.mpr ⟨hpData.1, by omega⟩

/-- Every canonical neighbourhood lies inside `[1,n)`. -/
theorem canonicalNeighbourhood_subset_unitInterval
    (n : ℕ) (a : ℕ → ℕ) (label : CanonicalBlockLabel) :
    canonicalNeighbourhood n a label ⊆ unitInterval n := by
  intro x hx
  exact (mem_canonicalNeighbourhood.mp hx).1

/-- Every point in `[1,n)` has at least one prime axis below saturation. -/
theorem supportedPrimes_nonempty_of_mem_unitInterval {n x : ℕ}
    (hx : x ∈ unitInterval n) :
    (supportedPrimes n x).Nonempty := by
  have hxBounds := mem_unitInterval.mp hx
  have hx0 : x ≠ 0 := by omega
  obtain ⟨p, hp⟩ := Nat.exists_factorization_lt_of_lt hx0 hxBounds.2
  have hnFactor : n.factorization p ≠ 0 := by omega
  have hpSupport : p ∈ n.factorization.support :=
    Finsupp.mem_support_iff.mpr hnFactor
  have hpFactors : p ∈ n.primeFactors := by simpa using hpSupport
  exact ⟨p, mem_supportedPrimes.mpr ⟨hpFactors, hp⟩⟩

/-- The represented canonical labels cover the entire natural-number universe. -/
theorem unitInterval_subset_biUnion_canonicalLabels (n : ℕ) (a : ℕ → ℕ) :
    unitInterval n ⊆
      (canonicalLabels n a).biUnion (canonicalNeighbourhood n a) := by
  intro x hx
  obtain ⟨p, hp⟩ := supportedPrimes_nonempty_of_mem_unitInterval hx
  exact Finset.mem_biUnion.mpr
    ⟨pointLabel a p x, pointLabel_mem_canonicalLabels hx hp,
      point_mem_canonicalNeighbourhood hx⟩

/-- The union of all represented canonical blocks is exactly `[1,n)`. -/
@[simp]
theorem biUnion_canonicalLabels (n : ℕ) (a : ℕ → ℕ) :
    (canonicalLabels n a).biUnion (canonicalNeighbourhood n a) = unitInterval n := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨label, _, hxLabel⟩ := Finset.mem_biUnion.mp hx
    exact canonicalNeighbourhood_subset_unitInterval n a label hxLabel
  · exact unitInterval_subset_biUnion_canonicalLabels n a

/-- The available canonical labels incident with one point. -/
def incidentLabels (n : ℕ) (a : ℕ → ℕ) (x : ℕ) : Finset CanonicalBlockLabel :=
  (canonicalLabels n a).filter fun label ↦ x ∈ canonicalNeighbourhood n a label

@[simp]
theorem mem_incidentLabels {n x : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel} :
    label ∈ incidentLabels n a x ↔
      label ∈ canonicalLabels n a ∧ x ∈ canonicalNeighbourhood n a label := by
  simp [incidentLabels]

/-- Incident labels are exactly the point labels on its supported prime axes. -/
theorem incidentLabels_eq_image_supportedPrimes
    {n x : ℕ} {a : ℕ → ℕ} (hx : x ∈ unitInterval n) :
    incidentLabels n a x = (supportedPrimes n x).image fun p ↦ pointLabel a p x := by
  ext label
  constructor
  · intro hlabel
    have hdata := mem_incidentLabels.mp hlabel
    have hp := labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood
      hdata.1 hdata.2
    exact Finset.mem_image.mpr
      ⟨label.prime, hp,
        pointLabel_eq_of_mem_canonicalNeighbourhood hdata.1 hdata.2⟩
  · intro hlabel
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hlabel
    exact mem_incidentLabels.mpr
      ⟨pointLabel_mem_canonicalLabels hx hp,
        point_mem_canonicalNeighbourhood hx⟩

/-- The number of labels incident with `x` is the number of its supported axes. -/
theorem card_incidentLabels {n x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ unitInterval n) :
    (incidentLabels n a x).card = (supportedPrimes n x).card := by
  rw [incidentLabels_eq_image_supportedPrimes hx]
  exact Finset.card_image_of_injective _ (pointLabel_injective a x)

/-- A point is private to its `p`-label exactly when `p` is its only supported axis. -/
theorem isPrivatePoint_pointLabel_iff_supportedPrimes_eq_singleton
    {n p x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ unitInterval n) (hp : p ∈ supportedPrimes n x) :
    IsPrivatePoint (canonicalLabels n a) (canonicalNeighbourhood n a)
        (pointLabel a p x) x ↔
      supportedPrimes n x = {p} := by
  constructor
  · intro hprivate
    apply Finset.Subset.antisymm
    · intro q hq
      have hEq := hprivate.2 (pointLabel a q x)
        (pointLabel_mem_canonicalLabels hx hq)
        (point_mem_canonicalNeighbourhood hx)
      exact Finset.mem_singleton.mpr (pointLabel_injective a x hEq)
    · intro q hq
      have hqp := Finset.mem_singleton.mp hq
      simpa [hqp] using hp
  · intro hsupport
    constructor
    · exact point_mem_canonicalNeighbourhood hx
    · intro label hlabel hxLabel
      have hpLabel := labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood
        hlabel hxLabel
      have hsingle : label.prime ∈ ({p} : Finset ℕ) := by
        rw [← hsupport]
        exact hpLabel
      have hprime : label.prime = p := Finset.mem_singleton.mp hsingle
      have hEq := pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hxLabel
      rw [hprime] at hEq
      exact hEq.symm

/-- A unique supported axis is the same as saturation on every other prime axis. -/
theorem supportedPrimes_eq_singleton_iff_saturatedOtherAxes
    {n p x : ℕ} (hp : p ∈ supportedPrimes n x) :
    supportedPrimes n x = {p} ↔
      ∀ q ∈ n.primeFactors, q ≠ p →
        n.factorization q ≤ x.factorization q := by
  constructor
  · intro hsupport q hqFactors hqp
    by_contra hnotLe
    have hqSupported : q ∈ supportedPrimes n x :=
      mem_supportedPrimes.mpr ⟨hqFactors, Nat.lt_of_not_ge hnotLe⟩
    have hqSingleton : q ∈ ({p} : Finset ℕ) := by
      rw [← hsupport]
      exact hqSupported
    exact hqp (Finset.mem_singleton.mp hqSingleton)
  · intro hsaturated
    apply Finset.Subset.antisymm
    · intro q hqSupported
      rw [Finset.mem_singleton]
      by_contra hqp
      have hqData := mem_supportedPrimes.mp hqSupported
      have hqSaturated := hsaturated q hqData.1 hqp
      omega
    · intro q hqSingleton
      have hqp := Finset.mem_singleton.mp hqSingleton
      simpa [hqp] using hp

/-- Private canonical labels are precisely labels generated by support-one points. -/
theorem isPrivateLabel_iff_exists_supportedPrimes_eq_singleton
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a) :
    IsPrivateLabel (canonicalLabels n a) (canonicalNeighbourhood n a) label ↔
      ∃ x ∈ unitInterval n,
        supportedPrimes n x = {label.prime} ∧
          pointLabel a label.prime x = label := by
  constructor
  · rintro ⟨x, hxPrivate⟩
    have hx := (mem_canonicalNeighbourhood.mp hxPrivate.1).1
    have hpoint := pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hxPrivate.1
    have hp := labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood
      hlabel hxPrivate.1
    have hprivatePoint :
        IsPrivatePoint (canonicalLabels n a) (canonicalNeighbourhood n a)
          (pointLabel a label.prime x) x := by
      simpa [hpoint] using hxPrivate
    have hsupport :=
      (isPrivatePoint_pointLabel_iff_supportedPrimes_eq_singleton hx hp).mp
        hprivatePoint
    exact ⟨x, hx, hsupport, hpoint⟩
  · rintro ⟨x, hx, hsupport, hpoint⟩
    have hp : label.prime ∈ supportedPrimes n x := by
      rw [hsupport]
      simp
    have hprivatePoint :=
      (isPrivatePoint_pointLabel_iff_supportedPrimes_eq_singleton (a := a) hx hp).mpr
        hsupport
    exact ⟨x, by simpa [hpoint] using hprivatePoint⟩

/-- Private labels are exactly those containing a point saturated on every other axis. -/
theorem isPrivateLabel_iff_exists_saturatedOtherAxes
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a) :
    IsPrivateLabel (canonicalLabels n a) (canonicalNeighbourhood n a) label ↔
      ∃ x ∈ canonicalNeighbourhood n a label,
        ∀ q ∈ n.primeFactors, q ≠ label.prime →
          n.factorization q ≤ x.factorization q := by
  constructor
  · intro hprivate
    obtain ⟨x, hx, hsupport, hpoint⟩ :=
      (isPrivateLabel_iff_exists_supportedPrimes_eq_singleton hlabel).mp hprivate
    have hp : label.prime ∈ supportedPrimes n x := by
      rw [hsupport]
      simp
    have hsaturated :=
      (supportedPrimes_eq_singleton_iff_saturatedOtherAxes hp).mp hsupport
    have hxLabel : x ∈ canonicalNeighbourhood n a label := by
      rw [← hpoint]
      exact point_mem_canonicalNeighbourhood hx
    exact ⟨x, hxLabel, hsaturated⟩
  · rintro ⟨x, hxLabel, hsaturated⟩
    have hx := (mem_canonicalNeighbourhood.mp hxLabel).1
    have hp := labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood
      hlabel hxLabel
    have hsupport :=
      (supportedPrimes_eq_singleton_iff_saturatedOtherAxes hp).mpr hsaturated
    have hpoint := pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hxLabel
    exact (isPrivateLabel_iff_exists_supportedPrimes_eq_singleton hlabel).mpr
      ⟨x, hx, hsupport, hpoint⟩

/-- Points whose unique supported prime axis is `p`. -/
def supportOnePointsOnAxis (n p : ℕ) : Finset ℕ :=
  (unitInterval n).filter fun x ↦ supportedPrimes n x = {p}

/-- Labels generated by support-one points on axis `p`. -/
def seedLabelsOnAxis (n : ℕ) (a : ℕ → ℕ) (p : ℕ) :
    Finset CanonicalBlockLabel :=
  (supportOnePointsOnAxis n p).image fun x ↦ pointLabel a p x

/-- The full arithmetic support-one seed family, retaining its prime labels. -/
def supportOneSeedLabels (n : ℕ) (a : ℕ → ℕ) : Finset CanonicalBlockLabel :=
  n.primeFactors.biUnion fun p ↦ seedLabelsOnAxis n a p

@[simp]
theorem mem_supportOnePointsOnAxis {n p x : ℕ} :
    x ∈ supportOnePointsOnAxis n p ↔
      x ∈ unitInterval n ∧ supportedPrimes n x = {p} := by
  simp [supportOnePointsOnAxis]

@[simp]
theorem mem_seedLabelsOnAxis
    {n p : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel} :
    label ∈ seedLabelsOnAxis n a p ↔
      ∃ x ∈ unitInterval n,
        supportedPrimes n x = {p} ∧ pointLabel a p x = label := by
  constructor
  · intro hlabel
    obtain ⟨x, hx, hpoint⟩ := Finset.mem_image.mp hlabel
    have hxData := mem_supportOnePointsOnAxis.mp hx
    exact ⟨x, hxData.1, hxData.2, hpoint⟩
  · rintro ⟨x, hx, hsupport, hpoint⟩
    exact Finset.mem_image.mpr
      ⟨x, mem_supportOnePointsOnAxis.mpr ⟨hx, hsupport⟩, hpoint⟩

@[simp]
theorem mem_supportOneSeedLabels
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel} :
    label ∈ supportOneSeedLabels n a ↔
      ∃ p ∈ n.primeFactors, ∃ x ∈ unitInterval n,
        supportedPrimes n x = {p} ∧ pointLabel a p x = label := by
  simp [supportOneSeedLabels]

/-- The project extensional family obtained by deduplicating canonical labels. -/
def canonicalExtensionalFamily (n : ℕ) (a : ℕ → ℕ) : Finset (Finset ℕ) :=
  extensionalImage (canonicalLabels n a) (canonicalNeighbourhood n a)

/-- The support-one labels of the arithmetic canonical family. -/
noncomputable def canonicalPrivateLabels (n : ℕ) (a : ℕ → ℕ) :
    Finset CanonicalBlockLabel :=
  privateLabels (canonicalLabels n a) (canonicalNeighbourhood n a)

/-- The abstract private-label filter is exactly the arithmetic support-one seed family. -/
theorem canonicalPrivateLabels_eq_supportOneSeedLabels
    (n : ℕ) (a : ℕ → ℕ) :
    canonicalPrivateLabels n a = supportOneSeedLabels n a := by
  ext label
  constructor
  · intro hprivate
    change label ∈ privateLabels
      (canonicalLabels n a) (canonicalNeighbourhood n a) at hprivate
    have hdata := mem_privateLabels.mp hprivate
    obtain ⟨x, hx, hsupport, hpoint⟩ :=
      (isPrivateLabel_iff_exists_supportedPrimes_eq_singleton hdata.1).mp hdata.2
    have hp : label.prime ∈ supportedPrimes n x := by
      rw [hsupport]
      simp
    have hpFactors := (mem_supportedPrimes.mp hp).1
    exact mem_supportOneSeedLabels.mpr
      ⟨label.prime, hpFactors, x, hx, hsupport, hpoint⟩
  · intro hseed
    obtain ⟨p, _, x, hx, hsupport, hpoint⟩ :=
      mem_supportOneSeedLabels.mp hseed
    have hp : p ∈ supportedPrimes n x := by
      rw [hsupport]
      simp
    have hlabelPoint := pointLabel_mem_canonicalLabels (a := a) hx hp
    have hlabel : label ∈ canonicalLabels n a := by
      simpa [hpoint] using hlabelPoint
    have hprivatePoint :=
      (isPrivatePoint_pointLabel_iff_supportedPrimes_eq_singleton (a := a) hx hp).mpr
        hsupport
    have hprivateLabel :
        IsPrivateLabel (canonicalLabels n a) (canonicalNeighbourhood n a) label :=
      ⟨x, by simpa [hpoint] using hprivatePoint⟩
    change label ∈ privateLabels (canonicalLabels n a) (canonicalNeighbourhood n a)
    exact mem_privateLabels.mpr ⟨hlabel, hprivateLabel⟩

/-- The abstract private-label count is the arithmetic seed-family cardinality. -/
theorem card_canonicalPrivateLabels_eq_card_supportOneSeedLabels
    (n : ℕ) (a : ℕ → ℕ) :
    (canonicalPrivateLabels n a).card = (supportOneSeedLabels n a).card := by
  rw [canonicalPrivateLabels_eq_supportOneSeedLabels]

/-- The extensional seed residual of the arithmetic canonical family. -/
noncomputable def canonicalSeedResidual (n : ℕ) (a : ℕ → ℕ) :
    Finset (Finset ℕ) :=
  privateResidualImage (canonicalLabels n a) (canonicalNeighbourhood n a)

/-- The closed arithmetic expression for the support-one seed count. -/
def seedCountFormula (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors,
    (p - 1) * ∑ j ∈ Finset.range (n.factorization p), p ^ min (a p) j

/-- Deduplicating the arithmetic labels preserves their minimum cover number. -/
theorem canonicalLabelCoverNumber_eq_axisCover (n : ℕ) (a : ℕ → ℕ) :
    labelCoverNumber (canonicalLabels n a) (canonicalNeighbourhood n a) =
      axis_cover (canonicalExtensionalFamily n a) := by
  simpa [axis_cover, canonicalExtensionalFamily] using
    labelCoverNumber_eq_tau_extensionalImage
      (canonicalLabels n a) (canonicalNeighbourhood n a)

/-- Exact support-one decomposition for the arithmetic canonical family. -/
theorem axisCover_canonicalExtensionalFamily_eq_private_add_residual
    (n : ℕ) (a : ℕ → ℕ) :
    axis_cover (canonicalExtensionalFamily n a) =
      (canonicalPrivateLabels n a).card +
        axis_cover (canonicalSeedResidual n a) := by
  simpa [canonicalExtensionalFamily, canonicalPrivateLabels, canonicalSeedResidual] using
    axis_cover_extensionalImage_eq_privateLabels_add_residual
      (canonicalLabels n a) (canonicalNeighbourhood n a)

end ModularSchur.CanonicalBlocks
