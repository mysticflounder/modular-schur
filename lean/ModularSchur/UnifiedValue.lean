import ModularSchur.Basic
import ModularSchur.SingletonSafety

/-!
# Phase 7 Unified Theorem (key step)

The element `n := m / gcd(m, ℓ-1) ∈ ZMod m` is an unsafe singleton,
because `(ℓ - 1) * n ≡ 0 (mod m)`.

This is the core of the upper bound in the Phase 7 theorem:
`S_m(k, ℓ) ≤ m/gcd(m, ℓ-1) - 1`.
-/

namespace ModularSchur

open Finset Nat

variable {m ℓ : ℕ}

/-
The residue `n = m / gcd(m, ℓ-1)` is an unsafe singleton: `(ℓ-1) * n ≡ 0 (mod m)`.
-/
theorem unsafe_witness_residue (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    ((ℓ : ZMod m) - 1) * ((m / Nat.gcd m (ℓ - 1) : ℕ) : ZMod m) = 0 := by
  norm_cast;
  simp +decide [ Int.subNatNat_of_le ( by linarith : 1 ≤ ℓ ) ];
  rw_mod_cast [ ← Nat.mul_div_assoc ];
  · rw [ Nat.mul_comm, Nat.mul_div_assoc ];
    · rw [ ZMod.natCast_eq_zero_iff ];
      exact dvd_mul_right _ _;
    · exact Nat.gcd_dvd_right _ _;
  · exact Nat.gcd_dvd_left _ _

end ModularSchur