/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

module

public import ModularSchur.CanonicalResidualCoverTransport
public import ModularSchur.CanonicalSeedCount
public import Mathlib.Data.Nat.Totient

/-!
# Arithmetic organization of canonical labels by prime axis

This file separates the labelled arithmetic count from the cover argument.
It counts every valuation layer by a truncated reduced-residue enumeration,
sums those layer counts on each prime axis, and subtracts the closed seed
count used by the residual cover.
-/

@[expose] public section

namespace ModularSchur.CanonicalBlocks

open Classical Finset

/-- The canonical labels lying on one prime axis. -/
def axisLabels (n : ℕ) (a : ℕ → ℕ) (p : ℕ) :
    Finset CanonicalBlockLabel :=
  (canonicalLabels n a).filter fun label ↦ label.prime = p

/-- Points in `[1,n)` having a prescribed `p`-adic valuation. -/
def axisLayerPoints (n p t : ℕ) : Finset ℕ :=
  (unitInterval n).filter fun x ↦ x.factorization p = t

/-- Labels on axis `p` contributed by one valuation layer. -/
def axisLayerLabels (n : ℕ) (a : ℕ → ℕ) (p t : ℕ) :
    Finset CanonicalBlockLabel :=
  (axisLayerPoints n p t).image fun x ↦ pointLabel a p x

private theorem card_prime_coprime_Ico {p m : ℕ} (hp : p.Prime) :
    ((Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u).card = m - m / p := by
  have htotal := Finset.card_filter_add_card_filter_not
    (s := Finset.Ico 1 (m + 1)) (p := fun u ↦ p.Coprime u)
  have hnot :
      ((Finset.Ico 1 (m + 1)).filter fun u ↦ ¬p.Coprime u).card = m / p := by
    rw [show (Finset.Ico 1 (m + 1)).filter (fun u ↦ ¬p.Coprime u) =
      (Finset.Ioc 0 m).filter (fun u ↦ p ∣ u) by
        ext u
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
        rw [hp.coprime_iff_not_dvd, not_not]
        omega]
    exact Nat.Ioc_filter_dvd_card_eq_div m p
  have hcard : (Finset.Ico 1 (m + 1)).card = m := by simp
  omega

private theorem card_prime_coprime_Ico_pow {p k : ℕ} (hp : p.Prime) :
    ((Finset.Ico 1 (p ^ (k + 1) + 1)).filter fun u ↦ p.Coprime u).card =
      (p - 1) * p ^ k := by
  let q := p ^ (k + 1)
  have hpq : p ∣ q := by
    dsimp [q]
    rw [pow_succ']
    exact dvd_mul_right p (p ^ k)
  have hcopiff (u : ℕ) : q.Coprime u ↔ p.Coprime u := by
    dsimp [q]
    exact Nat.coprime_pow_left_iff (Nat.succ_pos k) p u
  have hset :
      (Finset.Ico 1 (q + 1)).filter (fun u ↦ p.Coprime u) =
        (Finset.range q).filter fun u ↦ q.Coprime u := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
    constructor
    · rintro ⟨⟨hu1, huq⟩, hcop⟩
      have hune : u ≠ q := by
        rintro rfl
        exact (hp.coprime_iff_not_dvd.mp hcop) hpq
      exact ⟨by omega, (hcopiff u).mpr hcop⟩
    · rintro ⟨huq, hcop⟩
      have hcop' := (hcopiff u).mp hcop
      have hu0 : u ≠ 0 := by
        rintro rfl
        simp [hp.ne_one] at hcop'
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hu0, by omega⟩, hcop'⟩
  change ((Finset.Ico 1 (q + 1)).filter fun u ↦ p.Coprime u).card = _
  rw [hset, ← Nat.totient_eq_card_coprime, Nat.totient_prime_pow_succ hp]
  exact Nat.mul_comm _ _

private theorem card_prime_coprime_mod_pow_of_lt {p k m : ℕ}
    (hp : p.Prime) (hm : m < p ^ (k + 1)) :
    (((Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u).image
      fun u ↦ u % p ^ (k + 1)).card = m - m / p := by
  have hinj : Set.InjOn (fun u ↦ u % p ^ (k + 1))
      ((Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u) := by
    intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp hu).1
    have hv' := (Finset.mem_filter.mp hv).1
    simp only [Finset.mem_Ico] at hu' hv'
    change u % p ^ (k + 1) = v % p ^ (k + 1) at huv
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at huv
    exact huv
  rw [Finset.card_image_of_injOn hinj, card_prime_coprime_Ico hp]

private theorem card_prime_coprime_mod_pow_of_ge {p k m : ℕ}
    (hp : p.Prime) (hm : p ^ (k + 1) ≤ m) :
    (((Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u).image
      fun u ↦ u % p ^ (k + 1)).card = (p - 1) * p ^ k := by
  let q := p ^ (k + 1)
  have hqpos : 0 < q := by exact pow_pos hp.pos (k + 1)
  have hpq : p ∣ q := by
    dsimp [q]
    rw [pow_succ']
    exact dvd_mul_right p (p ^ k)
  have himage :
      ((Finset.Ico 1 (m + 1)).filter (fun u ↦ p.Coprime u)).image (fun u ↦ u % q) =
        (Finset.Ico 1 (q + 1)).filter fun u ↦ p.Coprime u := by
    ext r
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨u, ⟨⟨hu1, hum⟩, hcop⟩, rfl⟩
      have hrlt : u % q < q := Nat.mod_lt u hqpos
      have hnot : ¬p ∣ u % q := by
        intro hpdvd
        apply (hp.coprime_iff_not_dvd.mp hcop)
        rw [Nat.dvd_iff_mod_eq_zero] at hpdvd ⊢
        rw [← Nat.mod_mod_of_dvd u hpq, hpdvd]
      have hr0 : u % q ≠ 0 := by
        intro hr
        apply hnot
        simp [hr]
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hr0, by omega⟩,
        hp.coprime_iff_not_dvd.mpr hnot⟩
    · rintro ⟨⟨hr1, hrq⟩, hcop⟩
      have hrne : r ≠ q := by
        rintro rfl
        exact (hp.coprime_iff_not_dvd.mp hcop) hpq
      have hrlt : r < q := by omega
      exact ⟨r, ⟨⟨hr1, by omega⟩, hcop⟩, Nat.mod_eq_of_lt hrlt⟩
  change (((Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u).image
    fun u ↦ u % q).card = _
  rw [himage]
  exact card_prime_coprime_Ico_pow hp

private theorem card_prime_coprime_mod_pow_eq_min {p k m : ℕ} (hp : p.Prime) :
    (((Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u).image
      fun u ↦ u % p ^ (k + 1)).card = min ((p - 1) * p ^ k) (m - m / p) := by
  by_cases hm : m < p ^ (k + 1)
  · have hsubset :
        (Finset.Ico 1 (m + 1)).filter (fun u ↦ p.Coprime u) ⊆
          (Finset.Ico 1 (p ^ (k + 1) + 1)).filter fun u ↦ p.Coprime u := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨by
        simp only [Finset.mem_Ico] at hu' ⊢
        omega, hu'.2⟩
    have hle := Finset.card_le_card hsubset
    rw [card_prime_coprime_Ico hp, card_prime_coprime_Ico_pow hp] at hle
    rw [card_prime_coprime_mod_pow_of_lt hp hm, min_eq_right hle]
  · have hge : p ^ (k + 1) ≤ m := by omega
    have hsubset :
        (Finset.Ico 1 (p ^ (k + 1) + 1)).filter (fun u ↦ p.Coprime u) ⊆
          (Finset.Ico 1 (m + 1)).filter fun u ↦ p.Coprime u := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨by
        simp only [Finset.mem_Ico] at hu' ⊢
        omega, hu'.2⟩
    have hle := Finset.card_le_card hsubset
    rw [card_prime_coprime_Ico_pow hp, card_prime_coprime_Ico hp] at hle
    rw [card_prime_coprime_mod_pow_of_ge hp hge, min_eq_left hle]

private theorem factorization_prime_pow_mul_of_coprime {p t u : ℕ}
    (hp : p.Prime) (hu : p.Coprime u) :
    (p ^ t * u).factorization p = t := by
  rw [Nat.factorization_mul_apply_of_coprime (hu.pow_left t),
    Nat.factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hu), add_zero]

private theorem pointLabel_prime_pow_mul_of_coprime
    {p t u : ℕ} {a : ℕ → ℕ} (hp : p.Prime) (hu : p.Coprime u) :
    pointLabel a p (p ^ t * u) =
      ⟨p, t, p ^ t * (u % p ^ (a p + 1))⟩ := by
  have hfactor : (p ^ t * u).factorization p = t :=
    factorization_prime_pow_mul_of_coprime (t := t) hp hu
  rw [pointLabel, hfactor]
  congr 1
  rw [show p ^ (a p + t + 1) = p ^ t * p ^ (a p + 1) by
    rw [← pow_add]
    congr 1
    omega]
  exact Nat.mul_mod_mul_left (p ^ t) u (p ^ (a p + 1))

private theorem scaled_unit_of_mem_axisLayerPoints
    {n p t x : ℕ} (hp : p.Prime) (hx : x ∈ axisLayerPoints n p t) :
    x / p ^ t ∈
      (Finset.Ico 1 ((n - 1) / p ^ t + 1)).filter fun u ↦ p.Coprime u := by
  have hxData : x ∈ unitInterval n ∧ x.factorization p = t := by
    simpa [axisLayerPoints] using hx
  have hx0 : x ≠ 0 := Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hxData.1).1
  have hpowdvd : p ^ t ∣ x :=
    (hp.pow_dvd_iff_le_factorization hx0).mpr (by omega)
  obtain ⟨u, rfl⟩ := hpowdvd
  have hpowpos : 0 < p ^ t := pow_pos hp.pos t
  have hxu := mem_unitInterval.mp hxData.1
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hxu
  have hule : u ≤ (n - 1) / p ^ t := by
    have hmul : p ^ t * u ≤ n - 1 := by omega
    have hdiv : (p ^ t * u) / p ^ t ≤ (n - 1) / p ^ t :=
      Nat.div_le_div_right hmul
    rw [Nat.mul_div_right u hpowpos] at hdiv
    exact hdiv
  have hcop : p.Coprime u := hp.coprime_iff_not_dvd.mpr (by
    intro hpdiv
    have hsuccdvd : p ^ (t + 1) ∣ p ^ t * u := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left (p ^ t) hpdiv
    have hle := (hp.pow_dvd_iff_le_factorization
      (mul_ne_zero hpowpos.ne' hu0)).mp hsuccdvd
    rw [hxData.2] at hle
    omega)
  rw [Nat.mul_div_right u hpowpos]
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr hu0, Nat.lt_succ_of_le hule⟩, hcop⟩

private theorem mem_axisLayerPoints_of_scaled_unit
    {n p t u : ℕ} (hp : p.Prime)
    (hu : u ∈ (Finset.Ico 1 ((n - 1) / p ^ t + 1)).filter fun v ↦ p.Coprime v) :
    p ^ t * u ∈ axisLayerPoints n p t := by
  have huData := Finset.mem_filter.mp hu
  have huBounds := Finset.mem_Ico.mp huData.1
  have hpowpos : 0 < p ^ t := pow_pos hp.pos t
  apply (show p ^ t * u ∈ unitInterval n ∧ (p ^ t * u).factorization p = t →
    p ^ t * u ∈ axisLayerPoints n p t by simp [axisLayerPoints])
  refine ⟨mem_unitInterval.mpr ⟨?_, ?_⟩,
    factorization_prime_pow_mul_of_coprime (t := t) hp huData.2⟩
  · exact Nat.mul_pos hpowpos (Nat.zero_lt_of_lt huBounds.1)
  · have hule : u ≤ (n - 1) / p ^ t := by omega
    have hmul : p ^ t * u ≤ n - 1 := calc
      p ^ t * u ≤ p ^ t * ((n - 1) / p ^ t) := Nat.mul_le_mul_left _ hule
      _ ≤ n - 1 := Nat.mul_div_le (n - 1) (p ^ t)
    have hn0 : n ≠ 0 := by
      have hmulpos : 0 < p ^ t * u :=
        Nat.mul_pos hpowpos (Nat.zero_lt_of_lt huBounds.1)
      omega
    exact hmul.trans_lt (Nat.sub_one_lt hn0)

private theorem axisLayerPoints_eq_scaled_units {n p t : ℕ} (hp : p.Prime) :
    axisLayerPoints n p t =
      ((Finset.Ico 1 ((n - 1) / p ^ t + 1)).filter fun u ↦ p.Coprime u).image
        fun u ↦ p ^ t * u := by
  ext x
  constructor
  · intro hx
    have hxData : x ∈ unitInterval n ∧ x.factorization p = t := by
      simpa [axisLayerPoints] using hx
    have hx0 : x ≠ 0 :=
      Nat.one_le_iff_ne_zero.mp (mem_unitInterval.mp hxData.1).1
    have hpowdvd : p ^ t ∣ x :=
      (hp.pow_dvd_iff_le_factorization hx0).mpr (by rw [hxData.2])
    exact Finset.mem_image.mpr ⟨x / p ^ t, scaled_unit_of_mem_axisLayerPoints hp hx,
      Nat.mul_div_cancel' hpowdvd⟩
  · intro hx
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    rw [← hux]
    exact mem_axisLayerPoints_of_scaled_unit hp hu

@[simp]
theorem mem_axisLabels {n p : ℕ} {a : ℕ → ℕ}
    {label : CanonicalBlockLabel} :
    label ∈ axisLabels n a p ↔
      label ∈ canonicalLabels n a ∧ label.prime = p := by
  simp [axisLabels]

@[simp]
theorem mem_axisLayerPoints {n p t x : ℕ} :
    x ∈ axisLayerPoints n p t ↔
      x ∈ unitInterval n ∧ x.factorization p = t := by
  simp [axisLayerPoints]

@[simp]
theorem mem_axisLayerLabels {n p t : ℕ} {a : ℕ → ℕ}
    {label : CanonicalBlockLabel} :
    label ∈ axisLayerLabels n a p t ↔
      ∃ x ∈ unitInterval n,
        x.factorization p = t ∧ pointLabel a p x = label := by
  constructor
  · intro hlabel
    obtain ⟨x, hx, hpoint⟩ := Finset.mem_image.mp hlabel
    exact ⟨x, (mem_axisLayerPoints.mp hx).1,
      (mem_axisLayerPoints.mp hx).2, hpoint⟩
  · rintro ⟨x, hx, hxt, hpoint⟩
    exact Finset.mem_image.mpr
      ⟨x, mem_axisLayerPoints.mpr ⟨hx, hxt⟩, hpoint⟩

theorem axisLabels_filter_layer_eq_axisLayerLabels
    {n p t : ℕ} {a : ℕ → ℕ}
    (hp : p ∈ n.primeFactors) (ht : t < n.factorization p) :
    (axisLabels n a p).filter (fun label ↦ label.layer = t) =
      axisLayerLabels n a p t := by
  ext label
  constructor
  · intro hlabel
    have haxis := (mem_axisLabels.mp (Finset.mem_filter.mp hlabel).1).2
    have hlayer := Finset.mem_filter.mp hlabel |>.2
    obtain ⟨x, hx, q, hq, hpoint⟩ := mem_canonicalLabels.mp
      (mem_axisLabels.mp (Finset.mem_filter.mp hlabel).1).1
    have hqp : q = p := by
      calc
        q = (pointLabel a q x).prime := by rfl
        _ = label.prime := congrArg CanonicalBlockLabel.prime hpoint
        _ = p := haxis
    have hxt : x.factorization p = t := by
      calc
        x.factorization p = (pointLabel a q x).layer := by
          rw [hqp]
          rfl
        _ = label.layer := congrArg CanonicalBlockLabel.layer hpoint
        _ = t := hlayer
    exact mem_axisLayerLabels.mpr ⟨x, hx, hxt, by simpa [hqp] using hpoint⟩
  · intro hlabel
    obtain ⟨x, hx, hxt, hpoint⟩ := mem_axisLayerLabels.mp hlabel
    have hps : p ∈ supportedPrimes n x :=
      mem_supportedPrimes.mpr ⟨hp, hxt ▸ ht⟩
    have hcanonical : pointLabel a p x ∈ canonicalLabels n a :=
      pointLabel_mem_canonicalLabels hx hps
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply mem_axisLabels.mpr
      refine ⟨?_, ?_⟩
      · rw [← hpoint]
        exact hcanonical
      · rw [← hpoint]
        rfl
    · rw [← hpoint]
      exact hxt

/-- The exact number of distinct labels represented in one prime-axis valuation layer. -/
theorem card_axisLayerLabels_eq_min
    {n p t : ℕ} {a : ℕ → ℕ} (hp : p.Prime) (_ht : t < n.factorization p) :
    (axisLayerLabels n a p t).card =
      min ((p - 1) * p ^ (a p))
        ((n - 1) / p ^ t - (n - 1) / p ^ (t + 1)) := by
  let units :=
    (Finset.Ico 1 ((n - 1) / p ^ t + 1)).filter fun u ↦ p.Coprime u
  let embed : ℕ → CanonicalBlockLabel := fun r ↦ ⟨p, t, p ^ t * r⟩
  have himage :
      units.image (fun u ↦ pointLabel a p (p ^ t * u)) =
        (units.image fun u ↦ u % p ^ (a p + 1)).image embed := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro u hu
    exact pointLabel_prime_pow_mul_of_coprime hp (Finset.mem_filter.mp hu).2
  have hinj : Function.Injective embed := by
    intro r s hrs
    have hresidue := congrArg CanonicalBlockLabel.residue hrs
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos t) hresidue
  rw [axisLayerLabels, axisLayerPoints_eq_scaled_units hp, Finset.image_image]
  change (units.image (fun u ↦ pointLabel a p (p ^ t * u))).card = _
  rw [himage, Finset.card_image_of_injective _ hinj,
    card_prime_coprime_mod_pow_eq_min hp]
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

theorem card_axisLabels_eq_sum_layers
    {n p : ℕ} {a : ℕ → ℕ} (hp : p ∈ n.primeFactors) :
    (axisLabels n a p).card =
      ∑ t ∈ Finset.range (n.factorization p),
        min ((p - 1) * p ^ (a p))
          ((n - 1) / p ^ t - (n - 1) / p ^ (t + 1)) := by
  calc
    (axisLabels n a p).card =
        ∑ t ∈ Finset.range (n.factorization p),
          ((axisLabels n a p).filter (fun label ↦ label.layer = t)).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro label hlabel
      have hcanonical := (mem_axisLabels.mp hlabel).1
      obtain ⟨x, hx, q, hq, hpoint⟩ := mem_canonicalLabels.mp hcanonical
      have hqp : q = p := by
        calc
          q = (pointLabel a q x).prime := by rfl
          _ = label.prime := congrArg CanonicalBlockLabel.prime hpoint
          _ = p := (mem_axisLabels.mp hlabel).2
      have hlt : x.factorization p < n.factorization p := by
        have hq' : p ∈ supportedPrimes n x := by simpa [hqp] using hq
        exact (mem_supportedPrimes.mp hq').2
      rw [← hpoint]
      simpa [hqp, pointLabel] using hlt
    _ = ∑ t ∈ Finset.range (n.factorization p),
          min ((p - 1) * p ^ (a p))
            ((n - 1) / p ^ t - (n - 1) / p ^ (t + 1)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [axisLabels_filter_layer_eq_axisLayerLabels hp (Finset.mem_range.mp ht),
        card_axisLayerLabels_eq_min (Nat.prime_of_mem_primeFactors hp)
          (Finset.mem_range.mp ht)]

/-- Closed seed count on one axis, in the orientation used by the total axis
count. -/
def axisSeedCountFormula (n : ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  (p - 1) * ∑ j ∈ Finset.range (n.factorization p), p ^ min (a p) j

theorem card_seedLabelsOnAxis_eq_axisSeedCountFormula
    {n p : ℕ} {a : ℕ → ℕ} (hp : p ∈ n.primeFactors) :
    (seedLabelsOnAxis n a p).card = axisSeedCountFormula n a p := by
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
  rw [hlayers, axisSeedCountFormula]
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
      exact Finset.sum_range_reflect (fun j ↦ p ^ min (a p) j)
        (n.factorization p)

/-- The residual labels on one prime axis. -/
def residualAxisLabels (n : ℕ) (a : ℕ → ℕ) (p : ℕ) :
    Finset CanonicalBlockLabel :=
  (canonicalSeedResidualLabels n a).filter fun label ↦ label.prime = p

theorem seedLabelsOnAxis_subset_axisLabels
    {n p : ℕ} {a : ℕ → ℕ} :
    seedLabelsOnAxis n a p ⊆ axisLabels n a p := by
  intro label hlabel
  obtain ⟨x, hx, hsupp, hpoint⟩ := mem_seedLabelsOnAxis.mp hlabel
  have hps : p ∈ supportedPrimes n x := by
    rw [hsupp]
    simp
  apply mem_axisLabels.mpr
  refine ⟨?_, ?_⟩
  · rw [← hpoint]
    exact pointLabel_mem_canonicalLabels hx hps
  · rw [← hpoint]
    rfl

theorem residualAxisLabels_eq_axisLabels_sdiff_seed
    {n p : ℕ} {a : ℕ → ℕ} :
    residualAxisLabels n a p = axisLabels n a p \ seedLabelsOnAxis n a p := by
  ext label
  constructor
  · intro hlabel
    have hres := (Finset.mem_filter.mp hlabel).1
    have haxis : label ∈ axisLabels n a p := by
      apply mem_axisLabels.mpr
      exact ⟨(Finset.mem_sdiff.mp hres).1, (Finset.mem_filter.mp hlabel).2⟩
    exact Finset.mem_sdiff.mpr ⟨haxis, by
      intro hseed
      apply (Finset.mem_sdiff.mp hres).2
      obtain ⟨x, hx, hsupp, hpoint⟩ := mem_seedLabelsOnAxis.mp hseed
      have hps : p ∈ supportedPrimes n x := by
        rw [hsupp]
        simp
      have hp : p ∈ n.primeFactors := (mem_supportedPrimes.mp hps).1
      exact mem_supportOneSeedLabels.mpr ⟨p, hp, x, hx, hsupp, hpoint⟩⟩
  · intro hlabel
    have haxis := (Finset.mem_sdiff.mp hlabel).1
    have hnotseed := (Finset.mem_sdiff.mp hlabel).2
    apply Finset.mem_filter.mpr
    refine ⟨?_, (mem_axisLabels.mp haxis).2⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_axisLabels.mp haxis).1, ?_⟩
    intro hseed
    apply hnotseed
    obtain ⟨q, hq, hqseed⟩ := Finset.mem_biUnion.mp hseed
    obtain ⟨x, hx, hsupp, hpoint⟩ := mem_seedLabelsOnAxis.mp hqseed
    have hqp : q = p := by
      calc
        q = (pointLabel a q x).prime := by rfl
        _ = label.prime := congrArg CanonicalBlockLabel.prime hpoint
        _ = p := (mem_axisLabels.mp haxis).2
    exact mem_seedLabelsOnAxis.mpr ⟨x, hx, by simpa [hqp] using hsupp,
      by simpa [hqp] using hpoint⟩

theorem card_residualAxisLabels_eq_card_axisLabels_sub_seed
    {n p : ℕ} {a : ℕ → ℕ} :
    (residualAxisLabels n a p).card =
      (axisLabels n a p).card - (seedLabelsOnAxis n a p).card := by
  rw [residualAxisLabels_eq_axisLabels_sdiff_seed]
  exact Finset.card_sdiff_of_subset
    (seedLabelsOnAxis_subset_axisLabels (n := n) (a := a) (p := p))

theorem card_residualAxisLabels_eq_card_axisLabels_sub_axisSeedCountFormula
    {n p : ℕ} {a : ℕ → ℕ} (hp : p ∈ n.primeFactors) :
    (residualAxisLabels n a p).card =
      (axisLabels n a p).card - axisSeedCountFormula n a p := by
  rw [card_residualAxisLabels_eq_card_axisLabels_sub_seed,
    card_seedLabelsOnAxis_eq_axisSeedCountFormula hp]

end ModularSchur.CanonicalBlocks
