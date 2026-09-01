/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import ModularSchur.IntegerBridge
import ModularSchur.K1Theorem
import ModularSchur.SigmaInfty

/-!
# Solution.lean — comparator solution module

This file `import`s the project and discharges every `sorry` from
`Challenge.lean`, restating the **identical** signature under the same
`ComparatorClaims.` name and proving it from the real project theorem.

Each `ComparatorClaims.*` statement is the mathlib-only inlining of a project theorem
(see `Challenge.lean` for the inlining recipe). The two `private` bridge lemmas
identify the inlined `Nat.findGreatest` expressions with the project's
`schurMod` / `schurModResidue` definitions: the only gap between inlined and
project form is that the project quantifies over the one-constructor `Prop`
structures `IsValidPartitionNat` / `IsValidPartition`, whereas the inlined form
spells the four fields as a conjunction. The two existentials are propositionally
equal (structure ↔ its fields), so the `Nat.findGreatest` values coincide. Every
`ComparatorClaims.*` theorem's `#print axioms` closure is `{propext, Classical.choice,
Quot.sound}` — see `comparator/axiom-audit.lean`.
-/

open scoped Classical

namespace ComparatorClaims

/-- Bridge: the project integer Schur number `schurMod` equals its mathlib-inlined
`Nat.findGreatest` form (the validity-partition structure unbundled to fields). -/
private lemma schurMod_bridge (m k ℓ : ℕ) :
    ModularSchur.schurMod m k ℓ =
      Nat.findGreatest
        (fun N => ∃ P : Fin k → Finset ℕ,
          (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
          (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
          (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
          (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m))
        (m - 1) := by
  unfold ModularSchur.schurMod
  congr 1
  funext N
  apply propext
  constructor
  · rintro ⟨P, hP⟩; exact ⟨P, hP.covers, hP.disjoint, hP.subset, hP.sumFree⟩
  · rintro ⟨P, hc, hd, hs, hf⟩; exact ⟨P, ⟨hc, hd, hs, hf⟩⟩

/-- Bridge: the project residue Schur number `schurModResidue` equals its
mathlib-inlined `Nat.findGreatest` form. -/
private lemma schurModResidue_bridge (m k ℓ : ℕ) :
    ModularSchur.schurModResidue m k ℓ =
      Nat.findGreatest
        (fun N => ∃ P : Fin k → Finset (ZMod m),
          (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
          (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
          (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
          (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
        (m - 1) := by
  unfold ModularSchur.schurModResidue
  congr 1
  funext N
  apply propext
  constructor
  · rintro ⟨P, hP⟩; exact ⟨P, hP.covers, hP.disjoint, hP.subset, hP.sumFree⟩
  · rintro ⟨P, hc, hd, hs, hf⟩; exact ⟨P, ⟨hc, hd, hs, hf⟩⟩

theorem schurMod_integerClosedForm (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset ℕ,
        (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
        (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m))
      (m - 1) = m / Nat.gcd m (ℓ - 1) - 1 := by
  rw [← schurMod_bridge]; exact ModularSchur.schurMod_eq m k ℓ hm hℓ hk

theorem schurMod_integerCap_isGreatest (m : ℕ) (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : ∃ P : Fin k → Finset ℕ,
        (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
        (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m)) :
    N ≤ Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset ℕ,
        (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
        (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m))
      (m - 1) := by
  rw [← schurMod_bridge]
  apply ModularSchur.schurMod_is_greatest hm
  obtain ⟨P, hc, hd, hs, hf⟩ := hN
  exact ⟨P, ⟨hc, hd, hs, hf⟩⟩

theorem noValidIntegerPartition_of_ge_modulus (m : ℕ) (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : m ≤ N) (P : Fin k → Finset ℕ)
    (hcov : ∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hsub : ∀ i, P i ⊆ Finset.Ioc 0 N)
    (hsf : ∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m) :
    False :=
  ModularSchur.no_valid_partition_of_ge_m hm hN P ⟨hcov, hdis, hsub, hsf⟩

theorem schurMod_integer_eq_residue (m k ℓ : ℕ) (hm : 2 ≤ m) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset ℕ,
        (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
        (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m))
      (m - 1)
    = Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) := by
  rw [← schurMod_bridge, ← schurModResidue_bridge]
  exact ModularSchur.schurMod_eq_schurModResidue m k ℓ hm

theorem schurModResidue_closedForm (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) = m / Nat.gcd m (ℓ - 1) - 1 := by
  rw [← schurModResidue_bridge]; exact ModularSchur.schurModResidue_eq m k ℓ hm hℓ hk

theorem schurModResidue_upperBound (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) ≤ m / Nat.gcd m (ℓ - 1) - 1 := by
  rw [← schurModResidue_bridge]; exact ModularSchur.schurModResidue_le m k ℓ hm hℓ

theorem schurModResidue_lowerBound (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    m / Nat.gcd m (ℓ - 1) - 1 ≤ Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) := by
  rw [← schurModResidue_bridge]; exact ModularSchur.le_schurModResidue m k ℓ hm hℓ hk

theorem singleton_sumFree_iff_nonzeroMultiple (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ZMod m) :
    (∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ ({r} : Finset (ZMod m))) →
        ∀ y ∈ ({r} : Finset (ZMod m)), (∑ i, f i) ≠ y)
      ↔ ((ℓ : ZMod m) - 1) * r ≠ 0 :=
  ModularSchur.singleton_sumFree_iff ℓ hℓ r

theorem criticalResidue_isUnsafe (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    ((ℓ : ZMod m) - 1) * ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) = 0 :=
  ModularSchur.unsafe_witness_residue hm hℓ

theorem zeroMem_notSumFree (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (C : Finset (ZMod m))
    (h0 : (0 : ZMod m) ∈ C) :
    ¬ (∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ C) → ∀ y ∈ C, (∑ i, f i) ≠ y) :=
  ModularSchur.not_sumFree_of_mem_zero ℓ hℓ C h0

theorem schurModResidue_oneColorClosedForm_of_le_modulus
    (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    Nat.findGreatest
      (fun N => ∃ P : Fin 1 → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) = min (ℓ - 1) (m / ℓ) := by
  rw [← schurModResidue_bridge]; exact ModularSchur.schurModResidue_k1 m ℓ hm hℓ hlm

theorem schurModResidue_oneColorClosedForm (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    Nat.findGreatest
      (fun N ↦ ∃ P : Fin 1 → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) =
        if ℓ ≤ m then min (ℓ - 1) (m / ℓ) else if ℓ % m = 1 then 0 else 1 := by
  rw [← schurModResidue_bridge]
  exact ModularSchur.schurModResidue_k1_all m ℓ hm hℓ

theorem sigmaInfty_card_le_minFacQuotient (m : ℕ) (hm : 2 ≤ m) (C : Finset (ZMod m))
    (h : ∃ g : ℕ, g ∣ m ∧ 2 ≤ g ∧
           ∀ a b, a ∈ C → b ∈ C → g ∣ ((b - a : ZMod m).val)) :
    C.card ≤ m / m.minFac :=
  ModularSchur.sigmaInfty_le m hm C h

end ComparatorClaims
