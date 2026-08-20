/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Challenge.lean — comparator challenge module (mathlib-only)

This file imports **mathlib only** and states the headline results of the
*modular Schur number* project (paper: "A uniform closed form for modular Schur
numbers `S_m(k,ℓ)`") as `sorry` stubs. A reviewer reads THIS file (not the
repository) to see exactly what is being claimed, in formal language, with no
need to trust any of the project's own definitions — every type and predicate
below is from mathlib.

`Solution.lean` (which `import`s the project) discharges each `sorry` with the
real, axiom-clean project theorem, restating the **identical** signature under
the same `Headline.` name. The leanprover/comparator run checks that the two
modules' statements are identical (and the proofs axiom-clean), so statement
drift between the two files cannot pass silently.

## How the project definitions are inlined here

Every project definition is replaced by its mathlib body so the statements are
self-contained:

* `IsEllSumFree m ℓ C` (no `(ℓ+1)`-tuple from `C` sums to a member) becomes the
  bare predicate `∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ C) → ∀ y ∈ C, ∑ i, f i ≠ y`.
* `IsSumFreeIntMod m ℓ S` is the same with `ℕ` sums taken `% m`.
* `stableResidues m N` (the residues of `{1,…,N}`) becomes
  `(Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)`.
* The validity-partition **structures** `IsValidPartition` / `IsValidPartitionNat`
  are unbundled: the four fields appear as an explicit conjunction (inside the
  `Nat.findGreatest` predicate) or as separate hypotheses.
* `schurMod m k ℓ` and `schurModResidue m k ℓ` (the integer- and residue-level
  modular Schur numbers, Definition 1.1 with the `N ≤ m-1` cap of Lemma 2.2
  baked into `Nat.findGreatest`) are spelled out as the full `Nat.findGreatest`
  expression.

`Nat.findGreatest` needs `DecidablePred`; `open scoped Classical` supplies it, as
in the project's own `noncomputable def`.

## Audit boundary — what is and isn't here

The 12 theorems below are exactly the project's **structural closed-form**
results whose statement is expressible with mathlib definitions alone, and whose
`#print axioms` closure is `{propext, Classical.choice, Quot.sound}` (sorry-free,
no `native_decide`). They are the paper's machine-verified content.

The repository ALSO contains a large `native_decide`-backed computational scan
tree (`ModularSchur/Generated/`, the residue-axis / deficit-growth / scanner
machinery) which verifies per-modulus tables. That line is an older computational
route subsumed by the structural proof; it is **not** part of this comparator
gate (its closure includes `Lean.ofReduceBool`). The gate covers the
mathlib-statable, kernel-axiom-clean structural surface only.
-/

open scoped Classical

namespace Headline

/-- **Theorem 1.2 (main result), integer form (Definition 1.1).**
`S_m(k,ℓ) = m / gcd(m, ℓ-1) - 1` for `m ≥ 2`, `ℓ ≥ 2`, `k ≥ m/gcd(m,ℓ-1) - 1`.
Here `S_m(k,ℓ)` is the greatest `N ≤ m-1` such that `{1,…,N} ⊆ ℕ` admits a
`k`-partition whose classes are `ℓ`-sum-free modulo `m`. -/
theorem schurMod_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset ℕ,
        (∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ Finset.Ioc 0 N) ∧
        (∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m))
      (m - 1) = m / Nat.gcd m (ℓ - 1) - 1 :=
  sorry

/-- **Definition correctness.** Any `N` admitting a valid integer `k`-partition is
`≤ schurMod m k ℓ`; together with Lemma 2.2 this shows the `N ≤ m-1` cap in the
`Nat.findGreatest` is lossless, i.e. `schurMod` is the unbounded "greatest `N`" of
Definition 1.1, not a weakened bounded version. -/
theorem schurMod_is_greatest (m : ℕ) (hm : 2 ≤ m) {ℓ k N : ℕ}
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
      (m - 1) :=
  sorry

/-- **Lemma 2.2 (universal upper bound, integer form).** For `N ≥ m`, no
`k`-partition of `{1,…,N}` into `ℓ`-sum-free-mod-`m` classes exists: the constant
tuple `(m,…,m; m)` is a sum-freeness violation in whichever class contains `m`. -/
theorem no_valid_partition_of_ge_m (m : ℕ) (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : m ≤ N) (P : Fin k → Finset ℕ)
    (hcov : ∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i)
    (hdis : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hsub : ∀ i, P i ⊆ Finset.Ioc 0 N)
    (hsf : ∀ i, ∀ f : Fin ℓ → ℕ, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) % m ≠ y % m) :
    False :=
  sorry

/-- **Lemma 2.1 (residue reduction).** The integer- and residue-level modular
Schur numbers agree (for `m ≥ 2`): partitioning `{1,…,N} ⊆ ℕ` is equivalent to
partitioning the residue set `{1,…,N} ⊆ ZMod m`. -/
theorem schurMod_eq_schurModResidue (m k ℓ : ℕ) (hm : 2 ≤ m) :
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
      (m - 1) :=
  sorry

/-- **Theorem 1.2 (main result), residue form** (= Theorem 3.1 ∧ Theorem 4.1).
`schurModResidue m k ℓ = m / gcd(m, ℓ-1) - 1` for `k ≥ m/gcd(m,ℓ-1) - 1`. -/
theorem schurModResidue_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) = m / Nat.gcd m (ℓ - 1) - 1 :=
  sorry

/-- **Theorem 3.1 (upper bound, residue form).** `schurModResidue m k ℓ ≤ n-1`,
where `n = m/gcd(m,ℓ-1)`: the residue `n` is unsafe as a singleton, so any class
containing it fails `ℓ`-sum-freeness once `N ≥ n`. -/
theorem schurModResidue_le (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) ≤ m / Nat.gcd m (ℓ - 1) - 1 :=
  sorry

/-- **Theorem 4.1 (lower bound, residue form).** `n-1 ≤ schurModResidue m k ℓ`
for `k ≥ n-1`: the all-singletons partition `{1},…,{n-1}` (padded with empties)
is valid, since each singleton `{r}` with `1 ≤ r < n` is `ℓ`-sum-free. -/
theorem le_schurModResidue (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    m / Nat.gcd m (ℓ - 1) - 1 ≤ Nat.findGreatest
      (fun N => ∃ P : Fin k → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) :=
  sorry

/-- **Lemma 2.3 (singleton safety).** A singleton `{r} ⊆ ZMod m` is `ℓ`-sum-free
iff `(ℓ-1)·r ≠ 0`. -/
theorem singleton_sumFree_iff (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ZMod m) :
    (∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ ({r} : Finset (ZMod m))) →
        ∀ y ∈ ({r} : Finset (ZMod m)), (∑ i, f i) ≠ y)
      ↔ ((ℓ : ZMod m) - 1) * r ≠ 0 :=
  sorry

/-- **Arithmetic crux of the upper bound.** The residue `n = m/gcd(m,ℓ-1)`
satisfies `(ℓ-1)·n ≡ 0 (mod m)`, so `ℓ·n ≡ n`: `n` is an unsafe singleton. -/
theorem unsafe_witness_residue (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    ((ℓ : ZMod m) - 1) * ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) = 0 :=
  sorry

/-- **Universal bound (zero is unsafe).** Any class containing `0 : ZMod m` is not
`ℓ`-sum-free (`ℓ·0 = 0`), for `ℓ ≥ 1`. -/
theorem not_sumFree_of_mem_zero (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (C : Finset (ZMod m))
    (h0 : (0 : ZMod m) ∈ C) :
    ¬ (∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ C) → ∀ y ∈ C, (∑ i, f i) ≠ y) :=
  sorry

/-- **D'orville–Sim–Wong–Ho Problem 1.3 (k=1 closed form).** For `2 ≤ ℓ ≤ m`,
`schurModResidue m 1 ℓ = min(ℓ-1, ⌊m/ℓ⌋)`. -/
theorem schurModResidue_k1 (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    Nat.findGreatest
      (fun N => ∃ P : Fin 1 → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) = min (ℓ - 1) (m / ℓ) :=
  sorry

/-- **σ∞ coset cardinality bound.** If the pairwise differences of `C ⊆ ZMod m`
all lie in a proper subgroup (divisible by some `g ∣ m`, `g ≥ 2`), then
`|C| ≤ m / minFac m`. -/
theorem sigmaInfty_le (m : ℕ) (hm : 2 ≤ m) (C : Finset (ZMod m))
    (h : ∃ g : ℕ, g ∣ m ∧ 2 ≤ g ∧
           ∀ a b, a ∈ C → b ∈ C → g ∣ ((b - a : ZMod m).val)) :
    C.card ≤ m / m.minFac :=
  sorry

end Headline
