/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.CanonicalSeedCount
import Mathlib.Data.Nat.ModEq

/-!
# Prime multiplication for canonical seed residuals

This file develops the arithmetic transport used to multiply a quotient by a
prime at stable depth.  The point map is multiplication by that prime.  It
applies both above a positive active depth and when a depth-zero prime is
inserted for the first time: supported axes, seed coverage, and the residual
point set all transport exactly.
-/

namespace ModularSchur.CanonicalBlocks

open Finset
open ModularSchur.AxisLabelledCover

/-- Multiplication by a positive number identifies `[1,n)` with the multiples
of that number in `[1,p*n)`. -/
theorem image_mul_unitInterval_eq_filter_dvd {n p : ℕ} (hp : 0 < p) :
    (unitInterval n).image (fun x ↦ p * x) =
      (unitInterval (p * n)).filter fun y ↦ p ∣ y := by
  ext y
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxBounds := mem_unitInterval.mp hx
    apply And.intro
    · exact mem_unitInterval.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr
            (mul_ne_zero hp.ne' (Nat.one_le_iff_ne_zero.mp hxBounds.1)),
          (Nat.mul_lt_mul_left hp).mpr hxBounds.2⟩
    · exact dvd_mul_right p x
  · rintro ⟨hy, ⟨x, rfl⟩⟩
    refine ⟨x, ?_, rfl⟩
    have hyBounds := mem_unitInterval.mp hy
    exact mem_unitInterval.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr fun hx0 ↦ by simp [hx0] at hyBounds,
        (Nat.mul_lt_mul_left hp).mp hyBounds.2⟩

/-- Multiplication by a positive number sends `[1,n)` into `[1,p*n)`. -/
theorem mul_mem_unitInterval_mul {n p x : ℕ} (hp : 0 < p)
    (hx : x ∈ unitInterval n) :
    p * x ∈ unitInterval (p * n) := by
  have hxBounds := mem_unitInterval.mp hx
  exact mem_unitInterval.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hp.ne' (Nat.one_le_iff_ne_zero.mp hxBounds.1)),
      (Nat.mul_lt_mul_left hp).mpr hxBounds.2⟩

/-- A multiple in `[1,p*n)` has its quotient in `[1,n)`. -/
theorem mem_unitInterval_of_mul_mem_unitInterval_mul {n p x : ℕ} (hp : 0 < p)
    (hx : p * x ∈ unitInterval (p * n)) :
    x ∈ unitInterval n := by
  have hxBounds := mem_unitInterval.mp hx
  exact mem_unitInterval.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr fun hx0 ↦ by simp [hx0] at hxBounds,
      (Nat.mul_lt_mul_left hp).mp hxBounds.2⟩

/-- Multiplying by a prime factor raises its exponent by one. -/
theorem factorization_mul_left_self_eq_succ_of_mem_primeFactors
    {n p : ℕ} (hp : p ∈ n.primeFactors) :
    (p * n).factorization p = n.factorization p + 1 := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  rw [Nat.factorization_mul hpPrime.ne_zero hn0, Finsupp.add_apply]
  simp [hpPrime.factorization, add_comm]

/-- Multiplication by a prime raises that prime's exponent by one, whether or
not the prime was already represented in the modulus. -/
theorem factorization_mul_left_self_eq_succ_of_prime
    {n p : ℕ} (hpPrime : p.Prime) (hn0 : n ≠ 0) :
    (p * n).factorization p = n.factorization p + 1 := by
  rw [Nat.factorization_mul hpPrime.ne_zero hn0, Finsupp.add_apply]
  simp [hpPrime.factorization, add_comm]

/-- Multiplication by a prime preserves the complete set of supported axes
when the modulus and point are multiplied together. -/
theorem supportedPrimes_mul_prime
    {n p x : ℕ} (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hx : x ∈ unitInterval n) :
    supportedPrimes (p * n) (p * x) = supportedPrimes n x := by
  have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hx).1
  have hprimeFactors : (p * n).primeFactors = insert p n.primeFactors := by
    rw [Nat.primeFactors_mul hpPrime.ne_zero hn0, hpPrime.primeFactors]
    simp
  ext q
  rw [mem_supportedPrimes, mem_supportedPrimes, hprimeFactors,
    Nat.factorization_mul hpPrime.ne_zero hx0,
    Nat.factorization_mul hpPrime.ne_zero hn0, Finsupp.add_apply,
    Finsupp.add_apply]
  by_cases hqp : q = p
  · subst q
    rw [Finset.mem_insert]
    simp only [true_or, true_and]
    rw [show p.factorization p = 1 by simp [hpPrime.factorization],
      Nat.add_lt_add_iff_left]
    constructor
    · intro hlt
      have hnFactor : n.factorization p ≠ 0 := by omega
      have hpSupport : p ∈ n.factorization.support :=
        Finsupp.mem_support_iff.mpr hnFactor
      exact ⟨by simpa using hpSupport, hlt⟩
    · exact fun h ↦ h.2
  · simp [hpPrime.factorization, hqp]

/-- Multiplication by an active prime preserves the complete set of supported
prime axes when the modulus is multiplied by the same prime. -/
theorem supportedPrimes_mul_activePrime
    {n p x : ℕ} (hp : p ∈ n.primeFactors) (hx : x ∈ unitInterval n) :
    supportedPrimes (p * n) (p * x) = supportedPrimes n x := by
  exact supportedPrimes_mul_prime
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hx

/-- The label map induced by multiplying points by a prime. -/
def primeMultiplicationLabelMap (a : ℕ → ℕ) (p : ℕ)
    (label : CanonicalBlockLabel) : CanonicalBlockLabel :=
  if label.prime = p then
    ⟨p, label.layer + 1, p * label.residue⟩
  else
    ⟨label.prime, label.layer,
      (p * label.residue) % labelModulus a label⟩

/-- Compatibility name for prime multiplication on labels in the active-prime
specialization. -/
abbrev activePrimeLabelMap := primeMultiplicationLabelMap

/-- Point labels follow `primeMultiplicationLabelMap` under multiplication by any
prime. -/
theorem pointLabel_mul_prime
    {n p q x : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hx : x ∈ unitInterval n) :
    pointLabel a q (p * x) = primeMultiplicationLabelMap a p (pointLabel a q x) := by
  have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hx).1
  by_cases hqp : q = p
  · subst q
    have hfactor : (p * x).factorization p = x.factorization p + 1 := by
      rw [Nat.factorization_mul hpPrime.ne_zero hx0, Finsupp.add_apply]
      simp [hpPrime.factorization, add_comm]
    have hmodulus :
        p ^ (a p + (x.factorization p + 1) + 1) =
          p * p ^ (a p + x.factorization p + 1) := by
      rw [show a p + (x.factorization p + 1) + 1 =
        (a p + x.factorization p + 1) + 1 by omega, pow_succ']
    simp only [pointLabel, primeMultiplicationLabelMap, if_pos, hfactor]
    rw [hmodulus, Nat.mul_mod_mul_left]
  · have hfactor : (p * x).factorization q = x.factorization q := by
      rw [Nat.factorization_mul hpPrime.ne_zero hx0, Finsupp.add_apply]
      simp [hpPrime.factorization, hqp]
    simp [pointLabel, primeMultiplicationLabelMap, labelModulus, hqp, hfactor, Nat.mul_mod]

/-- Compatibility specialization of `pointLabel_mul_prime` to a represented
active prime. -/
theorem pointLabel_mul_activePrime
    {n p q x : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hx : x ∈ unitInterval n) :
    pointLabel a q (p * x) = activePrimeLabelMap a p (pointLabel a q x) := by
  exact pointLabel_mul_prime (Nat.prime_of_mem_primeFactors hp) hx

/-- Equality of labels on a prime axis can be reflected through multiplication
by a prime. -/
theorem pointLabel_eq_of_mul_prime
    {n p q x y : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hqPrime : q.Prime)
    (hx : x ∈ unitInterval n) (hy : y ∈ unitInterval n)
    (hlabels : pointLabel a q (p * x) = pointLabel a q (p * y)) :
    pointLabel a q x = pointLabel a q y := by
  have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hx).1
  have hy0 : y ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hy).1
  have hfactorX :
      (p * x).factorization q = p.factorization q + x.factorization q := by
    rw [Nat.factorization_mul hpPrime.ne_zero hx0, Finsupp.add_apply]
  have hfactorY :
      (p * y).factorization q = p.factorization q + y.factorization q := by
    rw [Nat.factorization_mul hpPrime.ne_zero hy0, Finsupp.add_apply]
  have hlayerMul := congrArg CanonicalBlockLabel.layer hlabels
  change (p * x).factorization q = (p * y).factorization q at hlayerMul
  rw [hfactorX, hfactorY] at hlayerMul
  have hlayer : x.factorization q = y.factorization q := by omega
  rw [pointLabel, pointLabel, CanonicalBlockLabel.mk.injEq]
  refine ⟨rfl, hlayer, ?_⟩
  have hresidue := congrArg CanonicalBlockLabel.residue hlabels
  change
    (p * x) % q ^ (a q + (p * x).factorization q + 1) =
      (p * y) % q ^ (a q + (p * y).factorization q + 1) at hresidue
  by_cases hqp : q = p
  · subst q
    have hfactorXP : (p * x).factorization p = x.factorization p + 1 := by
      rw [hfactorX]
      simp [hpPrime.factorization, add_comm]
    have hfactorYP : (p * y).factorization p = y.factorization p + 1 := by
      rw [hfactorY]
      simp [hpPrime.factorization, add_comm]
    rw [hfactorXP, hfactorYP, hlayer] at hresidue
    let P := p ^ (a p + y.factorization p + 1)
    have hmodulus :
        p ^ (a p + (y.factorization p + 1) + 1) = p * P := by
      rw [show a p + (y.factorization p + 1) + 1 =
        (a p + y.factorization p + 1) + 1 by omega, pow_succ']
    rw [hmodulus] at hresidue
    have hnewMod :
        p * x ≡ p * y [MOD p * P] := hresidue
    have holdMod := Nat.ModEq.mul_left_cancel' hpPrime.ne_zero hnewMod
    rw [hlayer]
    exact holdMod
  · have hpFactorQ : p.factorization q = 0 := by
      simp [hpPrime.factorization, hqp]
    have hfactorXQ : (p * x).factorization q = x.factorization q := by
      rw [hfactorX, hpFactorQ, zero_add]
    have hfactorYQ : (p * y).factorization q = y.factorization q := by
      rw [hfactorY, hpFactorQ, zero_add]
    rw [hfactorXQ, hfactorYQ, hlayer] at hresidue
    let Q := q ^ (a q + y.factorization q + 1)
    have hnewMod : p * x ≡ p * y [MOD Q] := by
      exact hresidue
    have hqNotDvdP : ¬q ∣ p := by
      intro hdiv
      exact hqp ((Nat.prime_dvd_prime_iff_eq hqPrime hpPrime).mp hdiv)
    have hpCoprimeQ : p.Coprime Q := by
      exact hqPrime.coprime_pow_of_not_dvd
        (m := a q + y.factorization q + 1) hqNotDvdP
    have holdMod := Nat.ModEq.cancel_left_of_coprime hpCoprimeQ.symm hnewMod
    rw [hlayer]
    exact holdMod

/-- Compatibility specialization of `pointLabel_eq_of_mul_prime` to old
represented prime axes. -/
theorem pointLabel_eq_of_mul_activePrime
    {n p q x y : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors)
    (hx : x ∈ unitInterval n) (hy : y ∈ unitInterval n)
    (hlabels : pointLabel a q (p * x) = pointLabel a q (p * y)) :
    pointLabel a q x = pointLabel a q y := by
  exact pointLabel_eq_of_mul_prime
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq) hx hy hlabels

/-- Multiplication by a prime preserves and reflects equality of point labels
on a prime axis. -/
theorem pointLabel_mul_prime_eq_iff
    {n p q x y : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hqPrime : q.Prime)
    (hx : x ∈ unitInterval n) (hy : y ∈ unitInterval n) :
    pointLabel a q (p * x) = pointLabel a q (p * y) ↔
      pointLabel a q x = pointLabel a q y := by
  constructor
  · exact pointLabel_eq_of_mul_prime hpPrime hqPrime hx hy
  · intro hlabels
    rw [pointLabel_mul_prime hpPrime hx, pointLabel_mul_prime hpPrime hy,
      hlabels]

/-- Compatibility specialization of `pointLabel_mul_prime_eq_iff` to old
represented prime axes. -/
theorem pointLabel_mul_activePrime_eq_iff
    {n p q x y : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors)
    (hx : x ∈ unitInterval n) (hy : y ∈ unitInterval n) :
    pointLabel a q (p * x) = pointLabel a q (p * y) ↔
      pointLabel a q x = pointLabel a q y := by
  exact pointLabel_mul_prime_eq_iff
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq) hx hy

/-- Points covered by at least one support-one seed label. -/
def canonicalSeedCoveredPoints (n : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  coveredPoints (supportOneSeedLabels n a) (canonicalNeighbourhood n a)

/-- Points left after deleting every point covered by a support-one seed label. -/
def canonicalSeedResidualPoints (n : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  unitInterval n \ canonicalSeedCoveredPoints n a

/-- Seed-covered points remain inside the canonical point universe. -/
theorem canonicalSeedCoveredPoints_subset_unitInterval (n : ℕ) (a : ℕ → ℕ) :
    canonicalSeedCoveredPoints n a ⊆ unitInterval n := by
  intro x hx
  change x ∈ coveredPoints (supportOneSeedLabels n a)
    (canonicalNeighbourhood n a) at hx
  obtain ⟨label, _, hxLabel⟩ := Finset.mem_biUnion.mp hx
  exact canonicalNeighbourhood_subset_unitInterval n a label hxLabel

@[simp]
theorem mem_canonicalSeedResidualPoints {n x : ℕ} {a : ℕ → ℕ} :
    x ∈ canonicalSeedResidualPoints n a ↔
      x ∈ unitInterval n ∧
        x ∉ canonicalSeedCoveredPoints n a := by
  simp [canonicalSeedResidualPoints]

/-- Among points divisible by a prime, seed coverage is transported exactly
by multiplication.  No stable-depth hypothesis is needed here. -/
theorem mul_mem_canonicalSeedCoveredPoints_iff_of_prime
    {n p x : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0) (hx : x ∈ unitInterval n) :
    p * x ∈ canonicalSeedCoveredPoints (p * n) a ↔
      x ∈ canonicalSeedCoveredPoints n a := by
  have hfactorPN := factorization_mul_left_self_eq_succ_of_prime hpPrime hn0
  constructor
  · intro hxCovered
    change p * x ∈ coveredPoints (supportOneSeedLabels (p * n) a)
      (canonicalNeighbourhood (p * n) a) at hxCovered
    obtain ⟨label, hseed, hxLabel⟩ := Finset.mem_biUnion.mp hxCovered
    obtain ⟨q, _, z, hz, hsupport, hpoint⟩ :=
      mem_supportOneSeedLabels.mp hseed
    subst label
    have hz0 : z ≠ 0 :=
      Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hz).1
    have hqSupportedZ : q ∈ supportedPrimes (p * n) z := by
      rw [hsupport]
      simp
    have hlabel := pointLabel_mem_canonicalLabels (a := a) hz hqSupportedZ
    have hnewLabels : pointLabel a q (p * x) = pointLabel a q z :=
      pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hxLabel
    have hpDvdZ : p ∣ z := by
      by_cases hqp : q = p
      · subst q
        have hlayerEq := congrArg CanonicalBlockLabel.layer hnewLabels
        change (p * x).factorization p = z.factorization p at hlayerEq
        have hx0 : x ≠ 0 :=
          Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hx).1
        have hfactorPX :
            (p * x).factorization p = x.factorization p + 1 := by
          rw [Nat.factorization_mul hpPrime.ne_zero hx0, Finsupp.add_apply]
          simp [hpPrime.factorization, add_comm]
        exact (hpPrime.dvd_iff_one_le_factorization hz0).2 (by omega)
      · have hpNotSupportedZ : p ∉ supportedPrimes (p * n) z := by
          rw [hsupport]
          simp [Ne.symm hqp]
        have hpFactorsPN : p ∈ (p * n).primeFactors := by
          rw [Nat.primeFactors_mul hpPrime.ne_zero hn0, hpPrime.primeFactors]
          simp
        have hpSaturated : (p * n).factorization p ≤ z.factorization p := by
          by_contra hnotLe
          exact hpNotSupportedZ (mem_supportedPrimes.mpr
            ⟨hpFactorsPN, Nat.lt_of_not_ge hnotLe⟩)
        exact (hpPrime.dvd_iff_one_le_factorization hz0).2 (by omega)
    rcases hpDvdZ with ⟨w, rfl⟩
    have hw : w ∈ unitInterval n :=
      mem_unitInterval_of_mul_mem_unitInterval_mul hpPrime.pos hz
    have hsupportOld : supportedPrimes n w = {q} := by
      rw [← supportedPrimes_mul_prime hpPrime hn0 hw]
      exact hsupport
    have hqSupportedOld : q ∈ supportedPrimes n w := by
      rw [hsupportOld]
      simp
    have hqFactorsOld := (mem_supportedPrimes.mp hqSupportedOld).1
    have holdLabels : pointLabel a q x = pointLabel a q w :=
      pointLabel_eq_of_mul_prime hpPrime
        (Nat.prime_of_mem_primeFactors hqFactorsOld) hx hw hnewLabels
    have hseedOld : pointLabel a q w ∈ supportOneSeedLabels n a :=
      mem_supportOneSeedLabels.mpr
        ⟨q, hqFactorsOld, w, hw, hsupportOld, rfl⟩
    change x ∈ coveredPoints (supportOneSeedLabels n a)
      (canonicalNeighbourhood n a)
    refine Finset.mem_biUnion.mpr ⟨pointLabel a q w, hseedOld, ?_⟩
    have hxOwnLabel := point_mem_canonicalNeighbourhood (a := a) (p := q) hx
    rwa [holdLabels] at hxOwnLabel
  · intro hxCovered
    change x ∈ coveredPoints (supportOneSeedLabels n a)
      (canonicalNeighbourhood n a) at hxCovered
    obtain ⟨label, hseed, hxLabel⟩ := Finset.mem_biUnion.mp hxCovered
    obtain ⟨q, hqFactors, z, hz, hsupport, hpoint⟩ :=
      mem_supportOneSeedLabels.mp hseed
    subst label
    have hqSupportedZ : q ∈ supportedPrimes n z := by
      rw [hsupport]
      simp
    have hlabel := pointLabel_mem_canonicalLabels (a := a) hz hqSupportedZ
    have holdLabels : pointLabel a q x = pointLabel a q z :=
      pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hxLabel
    have hpx := mul_mem_unitInterval_mul hpPrime.pos hx
    have hpz := mul_mem_unitInterval_mul hpPrime.pos hz
    have hsupportNew : supportedPrimes (p * n) (p * z) = {q} := by
      rw [supportedPrimes_mul_prime hpPrime hn0 hz]
      exact hsupport
    have hqSupportedNew : q ∈ supportedPrimes (p * n) (p * z) := by
      rw [hsupportNew]
      simp
    have hqFactorsNew := (mem_supportedPrimes.mp hqSupportedNew).1
    have hseedNew : pointLabel a q (p * z) ∈
        supportOneSeedLabels (p * n) a :=
      mem_supportOneSeedLabels.mpr
        ⟨q, hqFactorsNew, p * z, hpz, hsupportNew, rfl⟩
    have hnewLabels : pointLabel a q (p * x) = pointLabel a q (p * z) :=
      (pointLabel_mul_prime_eq_iff hpPrime
        (Nat.prime_of_mem_primeFactors hqFactors) hx hz).2 holdLabels
    change p * x ∈ coveredPoints (supportOneSeedLabels (p * n) a)
      (canonicalNeighbourhood (p * n) a)
    refine Finset.mem_biUnion.mpr ⟨pointLabel a q (p * z), hseedNew, ?_⟩
    have hpxOwnLabel := point_mem_canonicalNeighbourhood (a := a) (p := q) hpx
    rwa [hnewLabels] at hpxOwnLabel

/-- Compatibility specialization of seed-coverage transport to a represented
active prime. -/
theorem mul_mem_canonicalSeedCoveredPoints_iff
    {n p x : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hx : x ∈ unitInterval n) :
    p * x ∈ canonicalSeedCoveredPoints (p * n) a ↔
      x ∈ canonicalSeedCoveredPoints n a := by
  exact mul_mem_canonicalSeedCoveredPoints_iff_of_prime
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hx

/-- A represented valuation-zero label below the available exponent is already
generated by a point supported on only that prime axis. -/
theorem pointLabel_mem_supportOneSeedLabels_of_layer_zero
    {n p x : ℕ} {a : ℕ → ℕ}
    (hx : x ∈ unitInterval n) (hpSupported : p ∈ supportedPrimes n x)
    (hlayer : x.factorization p = 0)
    (hdepth : a p < n.factorization p) :
    pointLabel a p x ∈ supportOneSeedLabels n a := by
  let M := ordCompl[p] n
  let P := p ^ (a p + 1)
  have hxBounds := mem_unitInterval.mp hx
  have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hxBounds.1
  have hn0 : n ≠ 0 := by omega
  have hpFactors := (mem_supportedPrimes.mp hpSupported).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
  have hMpos : 0 < M := by
    simpa [M] using Nat.ordCompl_pos p hn0
  have hM0 : M ≠ 0 := hMpos.ne'
  have hPpos : 0 < P := by
    simpa [P] using pow_pos hpPrime.pos (a p + 1)
  have hP0 : P ≠ 0 := hPpos.ne'
  have hMP : M.Coprime P := by
    simpa [M, P] using (Nat.coprime_ordCompl hpPrime hn0).symm.pow_right (a p + 1)
  let y := (Nat.chineseRemainder hMP 0 x : ℕ)
  have hyMmod : y ≡ 0 [MOD M] := by
    simpa [y] using (Nat.chineseRemainder hMP 0 x).prop.1
  have hyxmod : y ≡ x [MOD P] := by
    simpa [y] using (Nat.chineseRemainder hMP 0 x).prop.2
  have hMdvdY : M ∣ y := Nat.modEq_zero_iff_dvd.mp hyMmod
  have hyltMP : y < M * P := by
    simpa [y] using Nat.chineseRemainder_lt_mul hMP 0 x hM0 hP0
  have hPle : P ≤ ordProj[p] n := by
    simpa [P] using
      Nat.pow_le_pow_right hpPrime.pos (show a p + 1 ≤ n.factorization p by omega)
  have hMPle : M * P ≤ n := by
    calc
      M * P ≤ M * ordProj[p] n := Nat.mul_le_mul_left M hPle
      _ = n := by
        rw [mul_comm]
        exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hy0 : y ≠ 0 := by
    intro hyZero
    have hxModZero : x ≡ 0 [MOD P] := by
      simpa [hyZero] using hyxmod.symm
    have hPdvdX : P ∣ x := Nat.modEq_zero_iff_dvd.mp hxModZero
    have hfactor := (hpPrime.pow_dvd_iff_le_factorization hx0).mp (by
      simpa [P] using hPdvdX)
    omega
  have hy : y ∈ unitInterval n :=
    mem_unitInterval.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hy0, lt_of_lt_of_le hyltMP hMPle⟩
  have hlabel := pointLabel_mem_canonicalLabels (a := a) hx hpSupported
  have hyLabel : y ∈ canonicalNeighbourhood n a (pointLabel a p x) :=
    mem_canonicalNeighbourhood.mpr
      ⟨hy, by simpa [Nat.ModEq, P, labelModulus, pointLabel, hlayer] using hyxmod⟩
  have hpointLabel : pointLabel a p y = pointLabel a p x := by
    exact pointLabel_eq_of_mem_canonicalNeighbourhood hlabel hyLabel
  have hpSupportedY : p ∈ supportedPrimes n y :=
    labelPrime_mem_supportedPrimes_of_mem_canonicalNeighbourhood hlabel hyLabel
  have hsaturated : ∀ q ∈ n.primeFactors, q ≠ p →
      n.factorization q ≤ y.factorization q := by
    intro q hqFactors hqp
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqFactors
    have hfactorM : M.factorization q = n.factorization q := by
      change (ordCompl[p] n).factorization q = n.factorization q
      rw [Nat.factorization_ordCompl, Finsupp.erase_ne hqp]
    have hpowDvdM : q ^ n.factorization q ∣ M :=
      (hqPrime.pow_dvd_iff_le_factorization hM0).2 (by simp [hfactorM])
    exact (hqPrime.pow_dvd_iff_le_factorization hy0).1 (hpowDvdM.trans hMdvdY)
  have hsupport : supportedPrimes n y = {p} :=
    (supportedPrimes_eq_singleton_iff_saturatedOtherAxes hpSupportedY).2 hsaturated
  exact mem_supportOneSeedLabels.mpr ⟨p, hpFactors, y, hy, hsupport, hpointLabel⟩

/-- Every represented valuation-zero label whose stable depth is below the
available exponent belongs to the support-one seed family. -/
theorem mem_supportOneSeedLabels_of_layer_zero
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a) (hlayer : label.layer = 0)
    (hdepth : a label.prime < n.factorization label.prime) :
    label ∈ supportOneSeedLabels n a := by
  obtain ⟨x, hx, p, hpSupported, hpoint⟩ := mem_canonicalLabels.mp hlabel
  subst label
  exact pointLabel_mem_supportOneSeedLabels_of_layer_zero hx hpSupported
    (by simpa [pointLabel] using hlayer) (by simpa [pointLabel] using hdepth)

/-- Once the exponent of an active prime has reached its stable depth, every
new valuation-zero label after adjoining one more copy of that prime is a
support-one seed. -/
theorem active_layerZero_mem_supportOneSeedLabels
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels (p * n) a)
    (hprime : label.prime = p) (hlayer : label.layer = 0) :
    label ∈ supportOneSeedLabels (p * n) a := by
  apply mem_supportOneSeedLabels_of_layer_zero hlabel hlayer
  rw [hprime, factorization_mul_left_self_eq_succ_of_mem_primeFactors hp]
  omega

/-- Below an available prime exponent, every point outside support-one seed
coverage is divisible by that prime. -/
theorem prime_dvd_of_mem_canonicalSeedResidualPoints
    {n p x : ℕ} {a : ℕ → ℕ} (hdepth : a p < n.factorization p)
    (hxResidual : x ∈ canonicalSeedResidualPoints n a) :
    p ∣ x := by
  by_contra hpNotDvd
  have hxData := mem_canonicalSeedResidualPoints.mp hxResidual
  have hnFactor : n.factorization p ≠ 0 := by omega
  have hpFactors : p ∈ n.primeFactors := by
    have hpSupport : p ∈ n.factorization.support :=
      Finsupp.mem_support_iff.mpr hnFactor
    simpa using hpSupport
  have hlayer : x.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpNotDvd
  have hpSupported : p ∈ supportedPrimes n x :=
    mem_supportedPrimes.mpr ⟨hpFactors, by omega⟩
  have hseed : pointLabel a p x ∈ supportOneSeedLabels n a :=
    pointLabel_mem_supportOneSeedLabels_of_layer_zero
      hxData.1 hpSupported hlayer hdepth
  apply hxData.2
  exact Finset.mem_biUnion.mpr
    ⟨pointLabel a p x, hseed, point_mem_canonicalNeighbourhood hxData.1⟩

/-- After adjoining one more copy of an active prime at or above its stable
depth, every residual point is a multiple of that prime. -/
theorem active_prime_dvd_of_mem_canonicalSeedResidualPoints
    {n p x : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p)
    (hxResidual : x ∈ canonicalSeedResidualPoints (p * n) a) :
    p ∣ x := by
  have hfactor := factorization_mul_left_self_eq_succ_of_mem_primeFactors hp
  apply prime_dvd_of_mem_canonicalSeedResidualPoints (a := a) (n := p * n)
    (p := p) (x := x) (by omega) hxResidual

/-- At stable depth, seed coverage after multiplying by a prime consists
exactly of all nonmultiples of that prime together with the image of the old
seed-covered points. -/
theorem canonicalSeedCoveredPoints_mul_prime_eq_nondvd_union_image
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    canonicalSeedCoveredPoints (p * n) a =
      ((unitInterval (p * n)).filter fun y ↦ ¬p ∣ y) ∪
        (canonicalSeedCoveredPoints n a).image fun x ↦ p * x := by
  have hfactor := factorization_mul_left_self_eq_succ_of_prime hpPrime hn0
  ext y
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hyCovered
    have hyUnit := canonicalSeedCoveredPoints_subset_unitInterval (p * n) a hyCovered
    by_cases hpDvdY : p ∣ y
    · right
      rcases hpDvdY with ⟨x, rfl⟩
      have hxUnit :=
        mem_unitInterval_of_mul_mem_unitInterval_mul hpPrime.pos hyUnit
      exact Finset.mem_image.mpr
        ⟨x, (mul_mem_canonicalSeedCoveredPoints_iff_of_prime
          hpPrime hn0 hxUnit).mp hyCovered, rfl⟩
    · exact Or.inl ⟨hyUnit, hpDvdY⟩
  · rintro (⟨hyUnit, hpNotDvdY⟩ | hyImage)
    · by_contra hyNotCovered
      have hyResidual : y ∈ canonicalSeedResidualPoints (p * n) a :=
        mem_canonicalSeedResidualPoints.mpr ⟨hyUnit, hyNotCovered⟩
      apply hpNotDvdY
      apply prime_dvd_of_mem_canonicalSeedResidualPoints
        (n := p * n) (p := p) (a := a) (x := y) ?_ hyResidual
      rw [hfactor]
      omega
    · obtain ⟨x, hxCovered, rfl⟩ := Finset.mem_image.mp hyImage
      have hxUnit := canonicalSeedCoveredPoints_subset_unitInterval n a hxCovered
      exact (mul_mem_canonicalSeedCoveredPoints_iff_of_prime
        hpPrime hn0 hxUnit).mpr hxCovered

/-- At stable depth, the enlarged residual point set is exactly the image of
the old residual set under multiplication by the prime. -/
theorem canonicalSeedResidualPoints_mul_prime_eq_image
    {n p : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    canonicalSeedResidualPoints (p * n) a =
      (canonicalSeedResidualPoints n a).image fun x ↦ p * x := by
  have hfactor := factorization_mul_left_self_eq_succ_of_prime hpPrime hn0
  ext y
  constructor
  · intro hyResidual
    have hyData := mem_canonicalSeedResidualPoints.mp hyResidual
    have hpDvdY : p ∣ y := by
      apply prime_dvd_of_mem_canonicalSeedResidualPoints
        (n := p * n) (p := p) (a := a) (x := y) ?_ hyResidual
      rw [hfactor]
      omega
    rcases hpDvdY with ⟨x, rfl⟩
    have hxUnit :=
      mem_unitInterval_of_mul_mem_unitInterval_mul hpPrime.pos hyData.1
    have hxNotCovered : x ∉ canonicalSeedCoveredPoints n a := by
      intro hxCovered
      exact hyData.2
        ((mul_mem_canonicalSeedCoveredPoints_iff_of_prime
          hpPrime hn0 hxUnit).mpr hxCovered)
    exact Finset.mem_image.mpr
      ⟨x, mem_canonicalSeedResidualPoints.mpr ⟨hxUnit, hxNotCovered⟩, rfl⟩
  · intro hyImage
    obtain ⟨x, hxResidual, rfl⟩ := Finset.mem_image.mp hyImage
    have hxData := mem_canonicalSeedResidualPoints.mp hxResidual
    exact mem_canonicalSeedResidualPoints.mpr
      ⟨mul_mem_unitInterval_mul hpPrime.pos hxData.1, fun hxCovered ↦
        hxData.2 ((mul_mem_canonicalSeedCoveredPoints_iff_of_prime
          hpPrime hn0 hxData.1).mp hxCovered)⟩

/-- Compatibility specialization of the stable-depth seed-coverage identity
to a represented active prime. -/
theorem canonicalSeedCoveredPoints_mul_eq_nondvd_union_image
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    canonicalSeedCoveredPoints (p * n) a =
      ((unitInterval (p * n)).filter fun y ↦ ¬p ∣ y) ∪
        (canonicalSeedCoveredPoints n a).image fun x ↦ p * x := by
  exact canonicalSeedCoveredPoints_mul_prime_eq_nondvd_union_image
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth

/-- Compatibility specialization of residual-point transport to a
represented active prime. -/
theorem canonicalSeedResidualPoints_mul_eq_image
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    canonicalSeedResidualPoints (p * n) a =
      (canonicalSeedResidualPoints n a).image fun x ↦ p * x := by
  exact canonicalSeedResidualPoints_mul_prime_eq_image
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth

end ModularSchur.CanonicalBlocks
