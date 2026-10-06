/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

module

public import ModularSchur.AllButOneAxisCover
public import ModularSchur.AxisBlockCount

/-!
# Closed numerical all-but-one-axis cover

The all-but-one-axis cover can be counted by partitioning its residual labels
according to their prime axes.  Each axis count is then the explicit valuation-
layer total with the closed support-one seed count removed.
-/

@[expose] public section

namespace ModularSchur.CanonicalBlocks

open Classical Finset
open ModularSchur.AxisLabelledCover
open ModularSchur.ResidueAxis

/-- The explicit total number of canonical labels on one prime axis. -/
def totalAxisCountFormula (n : ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n.factorization p),
    min ((p - 1) * p ^ (a p))
      ((n - 1) / p ^ t - (n - 1) / p ^ (t + 1))

/-- The explicit residual count on one prime axis. -/
def residualAxisCountFormula (n : ℕ) (a : ℕ → ℕ) (p : ℕ) : ℕ :=
  totalAxisCountFormula n a p - axisSeedCountFormula n a p

/-- Prime axes carrying a positive prescribed depth. -/
def activeAxes (n : ℕ) (a : ℕ → ℕ) : Finset ℕ :=
  n.primeFactors.filter fun p ↦ 0 < a p

private theorem prime_mem_primeFactors_of_mem_canonicalLabels
    {n : ℕ} {a : ℕ → ℕ} {label : CanonicalBlockLabel}
    (hlabel : label ∈ canonicalLabels n a) :
    label.prime ∈ n.primeFactors := by
  obtain ⟨x, hx, p, hp, hpoint⟩ := mem_canonicalLabels.mp hlabel
  rw [← hpoint]
  exact (mem_supportedPrimes.mp hp).1

/-- Residual labels off an axis split by their prime axis. -/
theorem card_residualLabelsExceptAxis_eq_sum_residualAxisLabels
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    (residualLabelsExceptAxis n a j).card =
      ∑ p ∈ n.primeFactors.erase j, (residualAxisLabels n a p).card := by
  have hcard :
      (residualLabelsExceptAxis n a j).card =
        ∑ p ∈ n.primeFactors.erase j,
          ((residualLabelsExceptAxis n a j).filter
            (fun label ↦ label.prime = p)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro label hlabel
    have hresidual := (Finset.mem_filter.mp hlabel).1
    have hcanonical := (Finset.mem_sdiff.mp hresidual).1
    have hp := prime_mem_primeFactors_of_mem_canonicalLabels hcanonical
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hlabel).2, hp⟩
  rw [hcard]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : p ≠ j := (Finset.mem_erase.mp hp).1
  have haxis :
      (residualLabelsExceptAxis n a j).filter (fun label ↦ label.prime = p) =
        residualAxisLabels n a p := by
    ext label
    constructor
    · intro hlabel
      have hfiltered := Finset.mem_filter.mp hlabel
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hfiltered.1).1, hfiltered.2⟩
    · intro hlabel
      have hfiltered := Finset.mem_filter.mp hlabel
      apply Finset.mem_filter.mpr
      refine ⟨?_, hfiltered.2⟩
      exact Finset.mem_filter.mpr
        ⟨hfiltered.1, by simpa [hfiltered.2] using hpj⟩
  rw [haxis]

theorem card_residualAxisLabels_eq_residualAxisCountFormula
    {n p : ℕ} {a : ℕ → ℕ} (hp : p ∈ n.primeFactors) :
    (residualAxisLabels n a p).card = residualAxisCountFormula n a p := by
  rw [residualAxisCountFormula,
    card_residualAxisLabels_eq_card_axisLabels_sub_axisSeedCountFormula hp,
    card_axisLabels_eq_sum_layers hp]
  rfl

/-- Residual labels off one axis have the explicit summed residual count. -/
theorem card_residualLabelsExceptAxis_eq_sum_residualAxisCountFormula
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    (residualLabelsExceptAxis n a j).card =
      ∑ p ∈ n.primeFactors.erase j, residualAxisCountFormula n a p := by
  rw [card_residualLabelsExceptAxis_eq_sum_residualAxisLabels]
  apply Finset.sum_congr rfl
  intro p hp
  exact card_residualAxisLabels_eq_residualAxisCountFormula
    (Finset.mem_erase.mp hp).2

/-- Closed numerical AB1 bound for an arbitrary omitted axis. -/
theorem axisCover_canonicalExtensionalFamily_le_seed_add_sum_residualAxisCountFormula
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ) :
    axis_cover (canonicalExtensionalFamily n a) ≤
      (supportOneSeedLabels n a).card +
        ∑ p ∈ n.primeFactors.erase j, residualAxisCountFormula n a p := by
  calc
    axis_cover (canonicalExtensionalFamily n a) ≤
        (supportOneSeedLabels n a).card +
          (residualLabelsExceptAxis n a j).card :=
      axisCover_canonicalExtensionalFamily_le_seed_add_residualLabelsExceptAxis n a j
    _ = (supportOneSeedLabels n a).card +
        ∑ p ∈ n.primeFactors.erase j, residualAxisCountFormula n a p := by
      rw [card_residualLabelsExceptAxis_eq_sum_residualAxisCountFormula]

/-- Closed AB2 bound, parameterized by an active axis maximizing the residual count. -/
theorem axisCover_canonicalExtensionalFamily_le_seed_add_sum_residualAxisCountFormula_sub_max
    (n : ℕ) (a : ℕ → ℕ) (j : ℕ)
    (hj : j ∈ activeAxes n a)
    (_hjmax : ∀ p ∈ activeAxes n a,
      residualAxisCountFormula n a p ≤ residualAxisCountFormula n a j) :
    axis_cover (canonicalExtensionalFamily n a) ≤
      (supportOneSeedLabels n a).card +
        ((∑ p ∈ n.primeFactors, residualAxisCountFormula n a p) -
          residualAxisCountFormula n a j) := by
  have hjFactors : j ∈ n.primeFactors := (Finset.mem_filter.mp hj).1
  have herase :
      (∑ p ∈ n.primeFactors.erase j, residualAxisCountFormula n a p) =
        (∑ p ∈ n.primeFactors, residualAxisCountFormula n a p) -
          residualAxisCountFormula n a j := by
    have hsum := Finset.sum_erase_add n.primeFactors
      (fun p ↦ residualAxisCountFormula n a p) hjFactors
    omega
  calc
    axis_cover (canonicalExtensionalFamily n a) ≤
        (supportOneSeedLabels n a).card +
          ∑ p ∈ n.primeFactors.erase j, residualAxisCountFormula n a p :=
      axisCover_canonicalExtensionalFamily_le_seed_add_sum_residualAxisCountFormula n a j
    _ = (supportOneSeedLabels n a).card +
        ((∑ p ∈ n.primeFactors, residualAxisCountFormula n a p) -
          residualAxisCountFormula n a j) := by
      rw [herase]

end ModularSchur.CanonicalBlocks
