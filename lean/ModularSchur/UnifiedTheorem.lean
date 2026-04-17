import ModularSchur.UnifiedValue
import ModularSchur.SingletonSafety

/-!
# Phase 7 Unified Theorem — upper bound for S_m(k,ℓ)

For all `m ≥ 2`, `ℓ ≥ 2`, `k ≥ 1`:

  S_m(k,ℓ) ≤ m / gcd(m, ℓ-1) - 1.

The key step (formalized here) is that the element `n := m / gcd(m,ℓ-1)`,
viewed as a residue in `ZMod m`, is an unsafe singleton — this forces any
class containing it to fail the ℓ-sum-free condition.

The partition-level upper bound follows from this residue-level statement
via Lemma 1.1 (residue reduction).
-/

namespace ModularSchur

open Finset Nat

variable {m ℓ : ℕ}

/-
The residue `n := m / gcd(m, ℓ-1) ∈ ZMod m` is not ℓ-safe as a singleton.
    Equivalently: any class `C ⊆ ZMod m` containing this residue is not
    `ℓ`-sum-free.
-/
theorem class_containing_n_not_sumFree (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (C : Finset (ZMod m))
    (hn : ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) ∈ C) :
    ¬ IsEllSumFree m ℓ C := by
  unfold IsEllSumFree;
  push_neg;
  refine' ⟨ fun _ => _, fun _ => hn, _, hn, _ ⟩;
  simp +decide;
  convert congr_arg ( fun x : ZMod m => x + ↑ ( m / m.gcd ( ℓ - 1 ) ) ) ( unsafe_witness_residue hm hℓ ) using 1 <;> ring

end ModularSchur