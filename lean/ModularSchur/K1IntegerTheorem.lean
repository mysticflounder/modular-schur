/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

module

public import ModularSchur.IntegerBridge
public import ModularSchur.K1Theorem

@[expose] public section

namespace ModularSchur

/-! The all-range one-color formula at the integer level. -/

/-- Complete one-color formula for the integer-level modular Schur number. -/
theorem schurMod_k1_all (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurMod m 1 ℓ =
      if ℓ ≤ m then min (ℓ - 1) (m / ℓ) else if ℓ % m = 1 then 0 else 1 := by
  rw [schurMod_eq_schurModResidue m 1 ℓ hm]
  exact schurModResidue_k1_all m ℓ hm hℓ

end ModularSchur
