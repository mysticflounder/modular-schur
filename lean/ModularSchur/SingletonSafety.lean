import ModularSchur.Basic

/-!
# Lemma 1.3: singleton safety

A singleton `{r} ⊆ ZMod m` is `ℓ`-sum-free iff `(ℓ - 1) * r ≠ 0` in `ZMod m`.

This is a direct reformulation of `ℓ * r ≠ r`.
-/

namespace ModularSchur

open Finset

variable {m : ℕ}

/-
Singleton safety.
-/
theorem singleton_sumFree_iff (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ZMod m) :
    IsEllSumFree m ℓ {r} ↔ ((ℓ : ZMod m) - 1) * r ≠ 0 := by
  constructor <;> intro h <;> simp_all +decide [ IsEllSumFree ];
  · exact fun hr => h ( fun _ => r ) ( fun _ => rfl ) ( by linear_combination hr );
  · grind

end ModularSchur