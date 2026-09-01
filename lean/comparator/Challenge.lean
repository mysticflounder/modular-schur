/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Challenge.lean — comparator challenge module (mathlib-only)

This file imports **mathlib only** and states the currently comparator-gated
structural results from the *modular Schur number* project (paper:
"Prime-power structure of the stable regime for modular Schur numbers") as
`sorry` stubs. A reviewer reads THIS file (not the repository) to see exactly
what is being claimed, in formal language, with no need to trust any of the
project's own definitions — every type and predicate below is from mathlib.

`Solution.lean` (which `import`s the project) discharges each `sorry` with the
real, axiom-clean project theorem, restating the **identical** signature under
the same `ComparatorClaims.` name. The leanprover/comparator run checks that the two
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

## Audit boundary — exact scope of the public claims

The 13 declarations below are deliberate `sorry`-backed statement stubs; this
file makes no proof claim by itself. The Comparator claim applies to the matching
declarations in `Solution.lean`: the gate checks statement identity, and their
measured `#print axioms` closure is exactly
`{propext, Classical.choice, Quot.sound}` (no `sorryAx`, custom axiom, or native
evaluation). These are the original paper's machine-verified structural results.
Newer project-wide theorem packages are recorded as non-gated planning stubs in
`comparator/README.md`; no declaration is added here until its complete
mathlib-only statement and matching project proof are ready.

The curated public snapshot also contains a 27-module hand-written,
generated-independent project layer plus `ModularSchur/PublicAxiomAudit.lean`.
That layer is outside the 13 Comparator declarations and has the separate build
and transitive-axiom-audit status recorded in `LEAN_STATUS.md`.

The private development checkout retains an older `native_decide`-backed
computational scan tree at `ModularSchur/Generated/`, together with
generated-dependent residue-axis, deficit-growth, and scanner modules. The
release assembler omits that tree and those dependent modules: they are absent
from the public repository snapshot, no public theorem depends on them, and they
are outside both public verification claims described above. Their historical
proof closures include generated per-computation native-evaluation axioms named
like `declaration._native.native_decide.ax_*`, so they do not satisfy the public
kernel-axiom boundary.
-/

open scoped Classical

namespace ComparatorClaims

/-- **Theorem 1.2 (main result), integer form (Definition 1.1).**
`S_m(k,ℓ) = m / gcd(m, ℓ-1) - 1` for `m ≥ 2`, `ℓ ≥ 2`, `k ≥ m/gcd(m,ℓ-1) - 1`.
Here `S_m(k,ℓ)` is the greatest `N ≤ m-1` such that `{1,…,N} ⊆ ℕ` admits a
`k`-partition whose classes are `ℓ`-sum-free modulo `m`. -/
theorem schurMod_integerClosedForm (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
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
      (m - 1) :=
  sorry

/-- **Lemma 2.2 (universal upper bound, integer form).** For `N ≥ m`, no
`k`-partition of `{1,…,N}` into `ℓ`-sum-free-mod-`m` classes exists: the constant
tuple `(m,…,m; m)` is a sum-freeness violation in whichever class contains `m`. -/
theorem noValidIntegerPartition_of_ge_modulus (m : ℕ) (hm : 2 ≤ m) {ℓ k N : ℕ}
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
      (m - 1) :=
  sorry

/-- **Theorem 1.2 (main result), residue form** (= Theorem 3.1 ∧ Theorem 4.1).
`schurModResidue m k ℓ = m / gcd(m, ℓ-1) - 1` for `k ≥ m/gcd(m,ℓ-1) - 1`. -/
theorem schurModResidue_closedForm (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
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
theorem schurModResidue_upperBound (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
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
theorem schurModResidue_lowerBound (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
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
theorem singleton_sumFree_iff_nonzeroMultiple (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ZMod m) :
    (∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ ({r} : Finset (ZMod m))) →
        ∀ y ∈ ({r} : Finset (ZMod m)), (∑ i, f i) ≠ y)
      ↔ ((ℓ : ZMod m) - 1) * r ≠ 0 :=
  sorry

/-- **Arithmetic crux of the upper bound.** The residue `n = m/gcd(m,ℓ-1)`
satisfies `(ℓ-1)·n ≡ 0 (mod m)`, so `ℓ·n ≡ n`: `n` is an unsafe singleton. -/
theorem criticalResidue_isUnsafe (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    ((ℓ : ZMod m) - 1) * ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) = 0 :=
  sorry

/-- **Universal bound (zero is unsafe).** Any class containing `0 : ZMod m` is not
`ℓ`-sum-free (`ℓ·0 = 0`), for `ℓ ≥ 1`. -/
theorem zeroMem_notSumFree (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) (C : Finset (ZMod m))
    (h0 : (0 : ZMod m) ∈ C) :
    ¬ (∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ C) → ∀ y ∈ C, (∑ i, f i) ≠ y) :=
  sorry

/-- **D'orville–Sim–Wong–Ho Problem 1.3 (k=1 closed form).** For `2 ≤ ℓ ≤ m`,
`schurModResidue m 1 ℓ = min(ℓ-1, ⌊m/ℓ⌋)`. -/
theorem schurModResidue_oneColorClosedForm_of_le_modulus
    (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    Nat.findGreatest
      (fun N => ∃ P : Fin 1 → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) = min (ℓ - 1) (m / ℓ) :=
  sorry

/-- **Complete one-color formula.** This extends Problem 1.3 to every
`m ≥ 2` and `ℓ ≥ 2`, including the two branches above the modulus. -/
theorem schurModResidue_oneColorClosedForm (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    Nat.findGreatest
      (fun N ↦ ∃ P : Fin 1 → Finset (ZMod m),
        (∀ x ∈ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m), ∃ i, x ∈ P i) ∧
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i, P i ⊆ (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)) ∧
        (∀ i, ∀ f : Fin ℓ → ZMod m, (∀ a, f a ∈ P i) → ∀ y ∈ P i, (∑ a, f a) ≠ y))
      (m - 1) =
        if ℓ ≤ m then min (ℓ - 1) (m / ℓ) else if ℓ % m = 1 then 0 else 1 :=
  sorry

/-- **σ∞ coset cardinality bound.** If the pairwise differences of `C ⊆ ZMod m`
all lie in a proper subgroup (divisible by some `g ∣ m`, `g ≥ 2`), then
`|C| ≤ m / minFac m`. -/
theorem sigmaInfty_card_le_minFacQuotient (m : ℕ) (hm : 2 ≤ m) (C : Finset (ZMod m))
    (h : ∃ g : ℕ, g ∣ m ∧ 2 ≤ g ∧
           ∀ a b, a ∈ C → b ∈ C → g ∣ ((b - a : ZMod m).val)) :
    C.card ≤ m / m.minFac :=
  sorry

end ComparatorClaims
