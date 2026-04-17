import ModularSchur.Basic
import ModularSchur.SingletonSafety

/-!
# Lemma 1.2: universal upper bound

Any class containing `0 : ZMod m` fails to be `ℓ`-sum-free (for `ℓ ≥ 1`),
since `ℓ · 0 = 0`. Equivalently, integers ≥ m cannot appear in any class.
-/

namespace ModularSchur

open Finset

variable {m : ℕ}

/-
Any class containing `0` is not `ℓ`-sum-free.
-/
theorem not_sumFree_of_mem_zero (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (C : Finset (ZMod m))
    (h0 : (0 : ZMod m) ∈ C) : ¬ IsEllSumFree m ℓ C := by
  unfold IsEllSumFree; aesop;

end ModularSchur