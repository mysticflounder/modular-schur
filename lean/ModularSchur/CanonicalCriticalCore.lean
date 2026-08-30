/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.CanonicalResidualCoverTransport

/-!
# Exponent truncation for canonical axes

This file iterates the stable-depth prime-multiplication recurrence.  It
reduces every prime exponent to its prescribed depth and records the removed
layers in a closed sum.  Prescribed depth zero is included: the prime is absent
from the truncated core and all of its exponent layers contribute to the sum.
-/

namespace ModularSchur.CanonicalBlocks

open Classical Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- The modulus obtained by truncating each prime exponent at its prescribed
active depth. -/
def exponentTruncatedCore (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ min (n.factorization p) (a p)

/-- The part of a prime exponent lying above its truncated value. -/
def exponentExcess (n : ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  n.factorization p - min (n.factorization p) (a p)

/-- The product of the prime powers removed by exponent truncation. -/
def excessExponentMultiplier (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ exponentExcess n a p

/-- The closed cover-number contribution of all exponent layers removed by
truncation. -/
def excessExponentContribution (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors,
    exponentExcess n a p * ((p - 1) * p ^ a p)

/-- The removed prime powers multiply the exponent-truncated core back to the
original nonzero modulus. -/
theorem excessExponentMultiplier_mul_exponentTruncatedCore
    {n : ℕ} (a : ℕ → ℕ) (hn0 : n ≠ 0) :
    excessExponentMultiplier n a * exponentTruncatedCore n a = n := by
  calc
    excessExponentMultiplier n a * exponentTruncatedCore n a =
        (∏ p ∈ n.primeFactors, p ^ exponentExcess n a p) *
          ∏ p ∈ n.primeFactors, p ^ min (n.factorization p) (a p) := rfl
    _ = ∏ p ∈ n.primeFactors,
        p ^ exponentExcess n a p *
          p ^ min (n.factorization p) (a p) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_add]
      congr 1
      exact Nat.sub_add_cancel (min_le_left _ _)
    _ = n := (Nat.prod_primeFactors_pow_factorization hn0).symm

/-- The exponent-truncated core is always nonzero. -/
theorem exponentTruncatedCore_ne_zero (n : ℕ) (a : ℕ → ℕ) :
    exponentTruncatedCore n a ≠ 0 := by
  rw [exponentTruncatedCore]
  exact Finset.prod_ne_zero_iff.mpr fun p hp ↦
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- Iterating multiplication by any prime at stable depth gives a closed
prime-power recurrence. -/
theorem axisCover_canonicalExtensionalFamily_primePow_mul_prime_eq
    {n p r : ℕ} {a : ℕ → ℕ}
    (hpPrime : p.Prime) (hn0 : n ≠ 0)
    (hdepth : a p ≤ n.factorization p) :
    axis_cover (canonicalExtensionalFamily (p ^ r * n) a) =
      axis_cover (canonicalExtensionalFamily n a) +
        r * ((p - 1) * p ^ a p) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hpow0 : p ^ r ≠ 0 := pow_ne_zero _ hpPrime.ne_zero
      have hbase0 : p ^ r * n ≠ 0 := mul_ne_zero hpow0 hn0
      have hdepthBase : a p ≤ (p ^ r * n).factorization p := by
        rw [Nat.factorization_mul hpow0 hn0, Finsupp.add_apply]
        omega
      calc
        axis_cover (canonicalExtensionalFamily (p ^ (r + 1) * n) a) =
            axis_cover (canonicalExtensionalFamily (p * (p ^ r * n)) a) := by
          congr 2
          rw [pow_succ]
          ac_rfl
        _ = axis_cover (canonicalExtensionalFamily (p ^ r * n) a) +
            (p - 1) * p ^ a p :=
          axisCover_canonicalExtensionalFamily_mul_prime_eq
            hpPrime hbase0 hdepthBase
        _ = (axis_cover (canonicalExtensionalFamily n a) +
              r * ((p - 1) * p ^ a p)) +
            (p - 1) * p ^ a p := by rw [ih]
        _ = axis_cover (canonicalExtensionalFamily n a) +
            (r + 1) * ((p - 1) * p ^ a p) := by
          rw [Nat.add_mul]
          omega

/-- Compatibility specialization of the prime-power recurrence to a
represented active prime. -/
theorem axisCover_canonicalExtensionalFamily_primePow_mul_eq
    {n p r : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hdepth : a p ≤ n.factorization p) :
    axis_cover (canonicalExtensionalFamily (p ^ r * n) a) =
      axis_cover (canonicalExtensionalFamily n a) +
        r * ((p - 1) * p ^ a p) := by
  exact axisCover_canonicalExtensionalFamily_primePow_mul_prime_eq
    (Nat.prime_of_mem_primeFactors hp)
    (Nat.mem_primeFactors.mp hp).2.2 hdepth

private theorem axisCover_canonicalExtensionalFamily_primePowerProduct_mul_prime_eq
    {n : ℕ} {a e : ℕ → ℕ} (s : Finset ℕ)
    (hn0 : n ≠ 0)
    (hprime : ∀ p ∈ s, e p ≠ 0 → p.Prime)
    (hstable : ∀ p ∈ s, e p ≠ 0 → a p ≤ n.factorization p) :
    axis_cover
        (canonicalExtensionalFamily ((∏ p ∈ s, p ^ e p) * n) a) =
      axis_cover (canonicalExtensionalFamily n a) +
        ∑ p ∈ s, e p * ((p - 1) * p ^ a p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hprimeS : ∀ q ∈ s, e q ≠ 0 → q.Prime := by
        intro q hq heq
        exact hprime q (Finset.mem_insert_of_mem hq) heq
      have hstableS : ∀ q ∈ s, e q ≠ 0 →
          a q ≤ n.factorization q := by
        intro q hq heq
        exact hstable q (Finset.mem_insert_of_mem hq) heq
      have ihS := ih hprimeS hstableS
      by_cases hep : e p = 0
      · simpa [Finset.prod_insert hp, Finset.sum_insert hp, hep] using ihS
      · have hpData := hstable p (Finset.mem_insert_self p s) hep
        have hpPrime := hprime p (Finset.mem_insert_self p s) hep
        have hprod0 : (∏ q ∈ s, q ^ e q) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro q hq
          by_cases heq : e q = 0
          · simp [heq]
          · exact pow_ne_zero _ (hprimeS q hq heq).ne_zero
        have hbase0 : (∏ q ∈ s, q ^ e q) * n ≠ 0 :=
          mul_ne_zero hprod0 hn0
        have hdepthBase :
            a p ≤ ((∏ q ∈ s, q ^ e q) * n).factorization p := by
          rw [Nat.factorization_mul hprod0 hn0, Finsupp.add_apply]
          omega
        calc
          axis_cover
              (canonicalExtensionalFamily
                ((∏ q ∈ insert p s, q ^ e q) * n) a) =
              axis_cover
                (canonicalExtensionalFamily
                  (p ^ e p * ((∏ q ∈ s, q ^ e q) * n)) a) := by
            rw [Finset.prod_insert hp]
            congr 2
            ac_rfl
          _ = axis_cover
                (canonicalExtensionalFamily
                  ((∏ q ∈ s, q ^ e q) * n) a) +
              e p * ((p - 1) * p ^ a p) :=
            axisCover_canonicalExtensionalFamily_primePow_mul_prime_eq
              hpPrime hbase0 hdepthBase
          _ = (axis_cover (canonicalExtensionalFamily n a) +
                ∑ q ∈ s, e q * ((q - 1) * q ^ a q)) +
              e p * ((p - 1) * p ^ a p) := by rw [ihS]
          _ = axis_cover (canonicalExtensionalFamily n a) +
              ∑ q ∈ insert p s, e q * ((q - 1) * q ^ a q) := by
            rw [Finset.sum_insert hp]
            omega

private theorem exponentTruncatedCore_stable_of_excess
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hpositive : 0 < a p)
    (hexcess : exponentExcess n a p ≠ 0) :
    p ∈ (exponentTruncatedCore n a).primeFactors ∧
      a p ≤ (exponentTruncatedCore n a).factorization p := by
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hba : n.factorization p - a p ≠ 0 := by
    simpa [exponentExcess, tsub_min] using hexcess
  have hlt : a p < n.factorization p :=
    Nat.sub_pos_iff_lt.mp (Nat.pos_of_ne_zero hba)
  have hmin : min (n.factorization p) (a p) = a p :=
    min_eq_right hlt.le
  have hcore0 := exponentTruncatedCore_ne_zero n a
  have hpowDvdCore :
      p ^ min (n.factorization p) (a p) ∣ exponentTruncatedCore n a := by
    rw [exponentTruncatedCore]
    exact Finset.dvd_prod_of_mem
      (fun q ↦ q ^ min (n.factorization q) (a q)) hp
  have hpaDvdCore : p ^ a p ∣ exponentTruncatedCore n a := by
    simpa [hmin] using hpowDvdCore
  have hpDvdCore : p ∣ exponentTruncatedCore n a := by
    exact (dvd_pow_self p (Nat.ne_of_gt hpositive)).trans hpaDvdCore
  refine ⟨Nat.mem_primeFactors.mpr ⟨hpPrime, hpDvdCore, hcore0⟩, ?_⟩
  have hfactorizationLe :
      (p ^ a p).factorization ≤ (exponentTruncatedCore n a).factorization :=
    (Nat.factorization_le_iff_dvd
      (pow_ne_zero _ hpPrime.ne_zero) hcore0).mpr hpaDvdCore
  simpa [hpPrime.factorization_pow] using hfactorizationLe p

/-- On an active quotient, the canonical cover number is its
exponent-truncated core cover number plus the closed contribution from all
removed exponent layers. -/
theorem axisCover_canonicalExtensionalFamily_eq_exponentTruncatedCore_add_excess
    (n : ℕ) (a : ℕ → ℕ) (hn0 : n ≠ 0)
    (hpositive : ∀ p ∈ n.primeFactors, 0 < a p) :
    axis_cover (canonicalExtensionalFamily n a) =
      axis_cover (canonicalExtensionalFamily (exponentTruncatedCore n a) a) +
        excessExponentContribution n a := by
  have hiteration :
      axis_cover
          (canonicalExtensionalFamily
            (excessExponentMultiplier n a * exponentTruncatedCore n a) a) =
        axis_cover
            (canonicalExtensionalFamily (exponentTruncatedCore n a) a) +
          excessExponentContribution n a := by
    simpa [excessExponentMultiplier, excessExponentContribution] using
      (axisCover_canonicalExtensionalFamily_primePowerProduct_mul_prime_eq
        (n := exponentTruncatedCore n a)
        (a := a) (e := exponentExcess n a) n.primeFactors
        (exponentTruncatedCore_ne_zero n a)
        (fun p hp _ ↦ Nat.prime_of_mem_primeFactors hp)
        (fun p hp hexcess ↦
          (exponentTruncatedCore_stable_of_excess hp
            (hpositive p hp) hexcess).2))
  calc
    axis_cover (canonicalExtensionalFamily n a) =
        axis_cover
          (canonicalExtensionalFamily
            (excessExponentMultiplier n a * exponentTruncatedCore n a) a) := by
      rw [excessExponentMultiplier_mul_exponentTruncatedCore a hn0]
    _ = axis_cover
          (canonicalExtensionalFamily (exponentTruncatedCore n a) a) +
        excessExponentContribution n a := hiteration

private theorem exponentTruncatedCore_depth_le_of_excess
    {n p : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (hexcess : exponentExcess n a p ≠ 0) :
    a p ≤ (exponentTruncatedCore n a).factorization p := by
  by_cases hzero : a p = 0
  · simp [hzero]
  · exact (exponentTruncatedCore_stable_of_excess hp
      (Nat.pos_of_ne_zero hzero) hexcess).2

/-- For arbitrary prescribed depths, the canonical cover number is its
exponent-truncated core cover number plus the closed contribution from every
removed exponent layer.  A depth-zero prime contributes all of its layers and
is absent from the core. -/
theorem axisCover_canonicalExtensionalFamily_eq_exponentTruncatedCore_add_excess_unrestricted
    (n : ℕ) (a : ℕ → ℕ) (hn0 : n ≠ 0) :
    axis_cover (canonicalExtensionalFamily n a) =
      axis_cover (canonicalExtensionalFamily (exponentTruncatedCore n a) a) +
        excessExponentContribution n a := by
  have hiteration :
      axis_cover
          (canonicalExtensionalFamily
            (excessExponentMultiplier n a * exponentTruncatedCore n a) a) =
        axis_cover
            (canonicalExtensionalFamily (exponentTruncatedCore n a) a) +
          excessExponentContribution n a := by
    simpa [excessExponentMultiplier, excessExponentContribution] using
      (axisCover_canonicalExtensionalFamily_primePowerProduct_mul_prime_eq
        (n := exponentTruncatedCore n a)
        (a := a) (e := exponentExcess n a) n.primeFactors
        (exponentTruncatedCore_ne_zero n a)
        (fun p hp _ ↦ Nat.prime_of_mem_primeFactors hp)
        (fun p hp hexcess ↦
          exponentTruncatedCore_depth_le_of_excess hp hexcess))
  calc
    axis_cover (canonicalExtensionalFamily n a) =
        axis_cover
          (canonicalExtensionalFamily
            (excessExponentMultiplier n a * exponentTruncatedCore n a) a) := by
      rw [excessExponentMultiplier_mul_exponentTruncatedCore a hn0]
    _ = axis_cover
          (canonicalExtensionalFamily (exponentTruncatedCore n a) a) +
        excessExponentContribution n a := hiteration

end ModularSchur.CanonicalBlocks
