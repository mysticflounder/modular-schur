import Mathlib

/-!
# Modular Schur numbers — basic definitions

We formalize D'orville–Sim–Wong–Ho (*Integers* 25 (2025) #A62) modular Schur
numbers `S_m(k,ℓ)` and the background needed for our unified theorem:

  S_m(k,ℓ) = m / gcd(m, ℓ-1) - 1  for  k ≥ m/gcd(m,ℓ-1) - 1.

The working convention: a subset `S ⊆ ℕ₊` is `ℓ`-sum-free mod `m` iff
whenever `x₁,…,x_ℓ ∈ S` (repetitions allowed) and `y ∈ S`, we have
`x₁ + ⋯ + x_ℓ ≢ y (mod m)`. `S_m(k,ℓ)` is the greatest `N` such that
`[1,N]` admits a `k`-partition into `ℓ`-sum-free sets.

In this formalization we work residue-by-residue in `ZMod m` — Lemma 1.1
(residue reduction) shows the partition problem on `[1,N]` for `N ≤ m-1`
reduces to the same problem on residues `{1,…,N} ⊆ ZMod m`.
-/

namespace ModularSchur

open Finset

/-- A subset `C ⊆ ZMod m` is **ℓ-sum-free mod m** iff no `(ℓ+1)`-tuple
    from `C` (with repetitions) satisfies `x₁ + ⋯ + x_ℓ = y`. -/
def IsEllSumFree (m : ℕ) (ℓ : ℕ) (C : Finset (ZMod m)) : Prop :=
  ∀ f : Fin ℓ → ZMod m, (∀ i, f i ∈ C) → ∀ y ∈ C, (∑ i, f i) ≠ y

end ModularSchur
