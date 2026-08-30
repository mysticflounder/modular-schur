/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.CanonicalBlocks
import Mathlib.Data.Nat.Totient

/-!
# Cardinality of arithmetic support-one seeds

This file counts the support-one labels of the arithmetic canonical family.  On a
prime axis `p`, valuation layer `j` contributes the totient of a prime power; summing
the layers and reflecting their order gives `seedCountFormula`.

## Main results

- `card_seedLabelsOnAxis_filter_layer`: cardinality of one prime-axis valuation layer.
- `card_supportOneSeedLabels_eq_seedCountFormula`: the closed support-one seed count.
- `axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual`: the exact
  canonical cover decomposition with its seed term in closed form.
-/

namespace ModularSchur.CanonicalBlocks

open Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- On prime axis `p`, layer `j` contributes the stated prime-power totient. -/
theorem card_seedLabelsOnAxis_filter_layer
    (n : ℕ) (a : ℕ → ℕ) {p j : ℕ}
    (hp : p ∈ n.primeFactors) (hj : j < n.factorization p) :
    ((seedLabelsOnAxis n a p).filter fun label ↦ label.layer = j).card =
      (p - 1) * p ^ min (a p) (n.factorization p - j - 1) := by
  let e := n.factorization p
  let M := ordCompl[p] n
  let unitsBelow (r : ℕ) := (Finset.Ico 0 (p ^ r)).filter fun u ↦ p.Coprime u
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  have hMpos : 0 < M := by
    simpa [M] using Nat.ordCompl_pos p hn0
  have hM0 : M ≠ 0 := hMpos.ne'
  have hMCoprime : p.Coprime M := by
    simpa [M] using Nat.coprime_ordCompl hpPrime hn0
  have hnEq : p ^ e * M = n := by
    simpa [e, M] using Nat.ordProj_mul_ordCompl_eq_self n p
  have hMFactorization : M.factorization = n.factorization.erase p := by
    simpa [M] using Nat.factorization_ordCompl n p
  have hpoints :
      (supportOnePointsOnAxis n p).filter (fun x ↦ x.factorization p = j) =
        (unitsBelow (e - j)).image (fun u ↦ M * (p ^ j * u)) := by
    ext x
    constructor
    · intro hx
      have hxData := Finset.mem_filter.mp hx
      have hxSupport := mem_supportOnePointsOnAxis.mp hxData.1
      have hx0 : x ≠ 0 := by
        have := (mem_unitInterval.mp hxSupport.1).1
        omega
      have hpSupported : p ∈ supportedPrimes n x := by
        rw [hxSupport.2]
        simp
      have hxSaturated :=
        (supportedPrimes_eq_singleton_iff_saturatedOtherAxes hpSupported).mp hxSupport.2
      have hMdiv : M ∣ x := by
        rw [← Nat.factorization_le_iff_dvd hM0 hx0]
        intro q
        by_cases hqp : q = p
        · subst q
          simp [hMFactorization]
        · by_cases hq0 : n.factorization q = 0
          · simp [hMFactorization, hqp, hq0]
          · have hqSupport : q ∈ n.factorization.support :=
              Finsupp.mem_support_iff.mpr hq0
            have hqFactors : q ∈ n.primeFactors := by simpa using hqSupport
            simpa [hMFactorization, hqp] using hxSaturated q hqFactors hqp
      let s := x / M
      have hMs : M * s = x := by
        simpa [s] using Nat.mul_div_cancel' hMdiv
      have hs0 : s ≠ 0 := by
        intro hs
        have : x = 0 := by simpa [hs] using hMs.symm
        exact hx0 this
      have hMFactorP : M.factorization p = 0 := by
        simp [hMFactorization]
      have hsFactor : s.factorization p = j := by
        rw [← hMs, Nat.factorization_mul hM0 hs0, Finsupp.add_apply,
          hMFactorP, zero_add] at hxData
        exact hxData.2
      have hpjDvd : p ^ j ∣ s :=
        (hpPrime.pow_dvd_iff_le_factorization hs0).2 (by simp [hsFactor])
      let u := s / p ^ j
      have hpu : p ^ j * u = s := by
        simpa [u] using Nat.mul_div_cancel' hpjDvd
      have hu0 : u ≠ 0 := by
        intro hu
        have : s = 0 := by simpa [hu] using hpu.symm
        exact hs0 this
      have huFactor : u.factorization p = 0 := by
        dsimp [u]
        rw [Nat.factorization_div hpjDvd]
        simp [hsFactor, hpPrime.factorization_pow]
      have huCoprime : p.Coprime u := by
        rw [hpPrime.coprime_iff_not_dvd]
        intro hpd
        have hone := (hpPrime.dvd_iff_one_le_factorization hu0).mp hpd
        omega
      have hsLt : s < p ^ e := by
        apply (Nat.mul_lt_mul_left hMpos).mp
        simpa [hMs, hnEq, mul_comm] using (mem_unitInterval.mp hxSupport.1).2
      have huLt : u < p ^ (e - j) := by
        apply (Nat.mul_lt_mul_left (pow_pos hpPrime.pos j)).mp
        rw [hpu, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hj)]
        exact hsLt
      exact Finset.mem_image.mpr
        ⟨u, by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨Nat.zero_le u, huLt⟩, huCoprime⟩,
          by simp [hMs, hpu]⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      have huData := Finset.mem_filter.mp hu
      have huLt := (Finset.mem_Ico.mp huData.1).2
      have huCoprime := huData.2
      have hu0 : u ≠ 0 := by
        intro hu
        subst u
        have hpOne : p = 1 := by simpa using huCoprime
        exact hpPrime.ne_one hpOne
      have hpu0 : p ^ j * u ≠ 0 := mul_ne_zero (pow_ne_zero _ hpPrime.ne_zero) hu0
      have hx0 : M * (p ^ j * u) ≠ 0 := mul_ne_zero hM0 hpu0
      have huFactor : u.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        exact Or.inr <| Or.inl <| (hpPrime.coprime_iff_not_dvd.mp huCoprime)
      have hpuFactor : (p ^ j * u).factorization p = j := by
        rw [Nat.factorization_mul (pow_ne_zero _ hpPrime.ne_zero) hu0,
          Finsupp.add_apply]
        simp [hpPrime.factorization_pow, huFactor]
      have hxFactor : (M * (p ^ j * u)).factorization p = j := by
        rw [Nat.factorization_mul hM0 hpu0, Finsupp.add_apply, hpuFactor]
        simp [hMFactorization]
      have hpuLt : p ^ j * u < p ^ e := by
        calc
          p ^ j * u < p ^ j * p ^ (e - j) :=
            (Nat.mul_lt_mul_left (pow_pos hpPrime.pos j)).2 huLt
          _ = p ^ e := by
            rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hj)]
      have hxLt : M * (p ^ j * u) < n := by
        rw [← hnEq]
        simpa [mul_comm] using (Nat.mul_lt_mul_left hMpos).2 hpuLt
      have hxUnit : M * (p ^ j * u) ∈ unitInterval n := by
        exact mem_unitInterval.mpr
          ⟨mul_pos hMpos (mul_pos (pow_pos hpPrime.pos j) (Nat.pos_of_ne_zero hu0)), hxLt⟩
      have hpSupported : p ∈ supportedPrimes n (M * (p ^ j * u)) :=
        mem_supportedPrimes.mpr ⟨hp, by rw [hxFactor]; simpa [e] using hj⟩
      have hxSaturated :
          ∀ q ∈ n.primeFactors, q ≠ p →
            n.factorization q ≤ (M * (p ^ j * u)).factorization q := by
        intro q hq hqp
        calc
          n.factorization q = M.factorization q := by simp [hMFactorization, hqp]
          _ ≤ (M * (p ^ j * u)).factorization q :=
            Nat.factorization_le_factorization_mul_left hpu0 q
      have hxSupport : supportedPrimes n (M * (p ^ j * u)) = {p} :=
        (supportedPrimes_eq_singleton_iff_saturatedOtherAxes hpSupported).2 hxSaturated
      exact Finset.mem_filter.mpr
        ⟨mem_supportOnePointsOnAxis.mpr ⟨hxUnit, hxSupport⟩, hxFactor⟩
  have hlabels :
      (seedLabelsOnAxis n a p).filter (fun label ↦ label.layer = j) =
        (unitsBelow (e - j)).image
          (fun u ↦ pointLabel a p (M * (p ^ j * u))) := by
    rw [seedLabelsOnAxis, Finset.filter_image]
    change ((supportOnePointsOnAxis n p).filter (fun x ↦ x.factorization p = j)).image
        (pointLabel a p) = _
    rw [hpoints, Finset.image_image]
    rfl
  let k := e - j
  let m := min (a p + 1) k
  have hkPos : 0 < k := by simp [k, e, Nat.sub_pos_of_lt hj]
  have hmPos : 0 < m := by
    exact lt_min (Nat.succ_pos (a p)) hkPos
  have hmLeK : m ≤ k := min_le_right _ _
  have hUnitsMono : unitsBelow m ⊆ unitsBelow k := by
    intro u hu
    have huData : u ∈ Finset.Ico 0 (p ^ m) ∧ p.Coprime u := by
      simpa [unitsBelow] using hu
    have huIco := Finset.mem_Ico.mp huData.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨huIco.1,
      huIco.2.trans_le (Nat.pow_le_pow_right hpPrime.pos hmLeK)⟩, huData.2⟩
  have hsmallImages :
      (unitsBelow k).image (fun u ↦ pointLabel a p (M * (p ^ j * u))) =
        (unitsBelow m).image (fun u ↦ pointLabel a p (M * (p ^ j * u))) := by
    by_cases hk : k ≤ a p + 1
    · have hm : m = k := min_eq_right hk
      simp [hm]
    · have hm : m = a p + 1 := min_eq_left (Nat.le_of_not_ge hk)
      ext label
      constructor
      · intro hlabel
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hlabel
        let v := u % p ^ m
        have huData : u ∈ Finset.Ico 0 (p ^ k) ∧ p.Coprime u := by
          simpa [unitsBelow] using hu
        have hvLt : v < p ^ m := Nat.mod_lt _ (pow_pos hpPrime.pos m)
        have huv : u ≡ v [MOD p ^ m] := by simp [Nat.ModEq, v]
        have hpDvdPow : p ∣ p ^ m := dvd_pow_self p hmPos.ne'
        have hvCoprime : p.Coprime v := by
          rw [hpPrime.coprime_iff_not_dvd]
          intro hpv
          exact (hpPrime.coprime_iff_not_dvd.mp huData.2) ((huv.dvd_iff hpDvdPow).2 hpv)
        have hv : v ∈ unitsBelow m := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨Nat.zero_le v, hvLt⟩, hvCoprime⟩
        have huPoint :
            M * (p ^ j * u) ∈
              (supportOnePointsOnAxis n p).filter (fun x ↦ x.factorization p = j) := by
          rw [hpoints]
          exact Finset.mem_image.mpr ⟨u, by simpa [k] using hu, rfl⟩
        have hvPoint :
            M * (p ^ j * v) ∈
              (supportOnePointsOnAxis n p).filter (fun x ↦ x.factorization p = j) := by
          rw [hpoints]
          exact Finset.mem_image.mpr ⟨v, by simpa [k] using hUnitsMono hv, rfl⟩
        have huFactor := (Finset.mem_filter.mp huPoint).2
        have hvFactor := (Finset.mem_filter.mp hvPoint).2
        have hscaled :
            M * (p ^ j * u) ≡ M * (p ^ j * v) [MOD p ^ (a p + j + 1)] := by
          have h := (huv.mul_left M).mul_left' (p ^ j)
          simpa [hm, pow_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
            mul_left_comm] using h
        exact Finset.mem_image.mpr
          ⟨v, hv, by simpa [pointLabel, huFactor, hvFactor, Nat.ModEq] using hscaled.symm⟩
      · intro hlabel
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hlabel
        exact Finset.mem_image.mpr ⟨u, hUnitsMono hu, rfl⟩
  have hInjective : Set.InjOn
      (fun u ↦ pointLabel a p (M * (p ^ j * u))) (unitsBelow m) := by
    intro u hu v hv huvLabel
    have huK := hUnitsMono hu
    have hvK := hUnitsMono hv
    have huPoint :
        M * (p ^ j * u) ∈
          (supportOnePointsOnAxis n p).filter (fun x ↦ x.factorization p = j) := by
      rw [hpoints]
      exact Finset.mem_image.mpr ⟨u, by simpa [k] using huK, rfl⟩
    have hvPoint :
        M * (p ^ j * v) ∈
          (supportOnePointsOnAxis n p).filter (fun x ↦ x.factorization p = j) := by
      rw [hpoints]
      exact Finset.mem_image.mpr ⟨v, by simpa [k] using hvK, rfl⟩
    have huFactor := (Finset.mem_filter.mp huPoint).2
    have hvFactor := (Finset.mem_filter.mp hvPoint).2
    have hscaled :
        M * (p ^ j * u) ≡ M * (p ^ j * v) [MOD p ^ (a p + j + 1)] := by
      simpa [pointLabel, huFactor, hvFactor, Nat.ModEq] using
        congrArg CanonicalBlockLabel.residue huvLabel
    have hcancelPow : M * u ≡ M * v [MOD p ^ (a p + 1)] := by
      apply Nat.ModEq.mul_left_cancel' (pow_ne_zero _ hpPrime.ne_zero)
      simpa [pow_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
        mul_left_comm] using hscaled
    have hcancelM : u ≡ v [MOD p ^ (a p + 1)] :=
      hcancelPow.cancel_left_of_coprime (hMCoprime.pow_left _)
    have hmodM : u ≡ v [MOD p ^ m] :=
      Nat.ModEq.of_dvd (pow_dvd_pow p (min_le_left _ _)) hcancelM
    exact hmodM.eq_of_lt_of_lt
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hu).1).2
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1).2
  have hcardUnits : (unitsBelow m).card = Nat.totient (p ^ m) := by
    simpa [unitsBelow, Nat.coprime_pow_left_iff hmPos] using
      Nat.filter_coprime_Ico_eq_totient (p ^ m) 0
  have hmSub : m - 1 = min (a p) (e - j - 1) := by
    simp [m, k]
    omega
  calc
    ((seedLabelsOnAxis n a p).filter fun label ↦ label.layer = j).card =
        ((unitsBelow m).image
          (fun u ↦ pointLabel a p (M * (p ^ j * u)))).card := by
      rw [hlabels]
      simpa [k] using congrArg Finset.card hsmallImages
    _ = (unitsBelow m).card := Finset.card_image_iff.mpr hInjective
    _ = Nat.totient (p ^ m) := hcardUnits
    _ = p ^ (m - 1) * (p - 1) := by
      simpa [Nat.sub_add_cancel hmPos] using Nat.totient_prime_pow_succ hpPrime (m - 1)
    _ = (p - 1) * p ^ min (a p) (n.factorization p - j - 1) := by
      simp [hmSub, e, mul_comm]

/-- The cardinality of the full support-one seed family is its closed arithmetic sum. -/
theorem card_supportOneSeedLabels_eq_seedCountFormula (n : ℕ) (a : ℕ → ℕ) :
    (supportOneSeedLabels n a).card = seedCountFormula n a := by
  have hdisjoint :
      (n.primeFactors : Set ℕ).PairwiseDisjoint (seedLabelsOnAxis n a) := by
    intro p hp q hq hpq
    change Disjoint (seedLabelsOnAxis n a p) (seedLabelsOnAxis n a q)
    rw [Finset.disjoint_left]
    intro label hpLabel hqLabel
    obtain ⟨x, _, _, hpx⟩ := mem_seedLabelsOnAxis.mp hpLabel
    obtain ⟨y, _, _, hqy⟩ := mem_seedLabelsOnAxis.mp hqLabel
    have hpqEq : p = q := by
      simpa [pointLabel] using
        congrArg CanonicalBlockLabel.prime (hpx.trans hqy.symm)
    exact hpq hpqEq
  have haxisCard (p : ℕ) (hp : p ∈ n.primeFactors) :
      (seedLabelsOnAxis n a p).card =
        (p - 1) * ∑ j ∈ Finset.range (n.factorization p), p ^ min (a p) j := by
    have hlayers :
        (seedLabelsOnAxis n a p).card =
          ∑ j ∈ Finset.range (n.factorization p),
            ((seedLabelsOnAxis n a p).filter fun label ↦ label.layer = j).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro label hlabel
      obtain ⟨x, _, hxSupport, hxLabel⟩ := mem_seedLabelsOnAxis.mp hlabel
      have hpSupported : p ∈ supportedPrimes n x := by
        rw [hxSupport]
        simp
      have hlt := (mem_supportedPrimes.mp hpSupported).2
      rw [← hxLabel]
      simpa [pointLabel] using hlt
    rw [hlayers]
    calc
      (∑ j ∈ Finset.range (n.factorization p),
          ((seedLabelsOnAxis n a p).filter fun label ↦ label.layer = j).card) =
          ∑ j ∈ Finset.range (n.factorization p),
            (p - 1) * p ^ min (a p) (n.factorization p - j - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact card_seedLabelsOnAxis_filter_layer n a hp (Finset.mem_range.mp hj)
      _ = (p - 1) *
          ∑ j ∈ Finset.range (n.factorization p),
            p ^ min (a p) (n.factorization p - 1 - j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        congr 2
        omega
      _ = (p - 1) * ∑ j ∈ Finset.range (n.factorization p), p ^ min (a p) j := by
        congr 1
        exact Finset.sum_range_reflect (fun j ↦ p ^ min (a p) j) (n.factorization p)
  rw [supportOneSeedLabels, Finset.card_biUnion hdisjoint, seedCountFormula]
  apply Finset.sum_congr rfl
  intro p hp
  exact haxisCard p hp

/-- The exact canonical cover decomposition with the support-one term in closed form. -/
theorem axisCover_canonicalExtensionalFamily_eq_seedCountFormula_add_residual
    (n : ℕ) (a : ℕ → ℕ) :
    axis_cover (canonicalExtensionalFamily n a) =
      seedCountFormula n a + axis_cover (canonicalSeedResidual n a) := by
  calc
    axis_cover (canonicalExtensionalFamily n a) =
        (canonicalPrivateLabels n a).card +
          axis_cover (canonicalSeedResidual n a) :=
      axisCover_canonicalExtensionalFamily_eq_private_add_residual n a
    _ = seedCountFormula n a + axis_cover (canonicalSeedResidual n a) := by
      rw [card_canonicalPrivateLabels_eq_card_supportOneSeedLabels,
        card_supportOneSeedLabels_eq_seedCountFormula]

end ModularSchur.CanonicalBlocks
