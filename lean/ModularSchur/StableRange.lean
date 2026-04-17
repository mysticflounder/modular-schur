import ModularSchur.SingletonSafety
import ModularSchur.UnifiedValue

/-!
# Phase 7 lower-bound witness

For `r ∈ {1, …, m/gcd(m,ℓ-1) - 1}`, the singleton `{r} ⊆ ZMod m` is
`ℓ`-sum-free. This is the building block of the lower-bound partition
in Phase 7 (singletons `{1}, {2}, …, {n-1}` each as their own class,
padded with empty classes to reach `k ≥ n - 1`).

Proof: by `singleton_sumFree_iff`, need `(ℓ-1)·r ≢ 0 (mod m)`.
Let `d = gcd(m, ℓ-1)`, `n = m/d`. Write `ℓ-1 = d·u` with `gcd(u, n) = 1`.
Then `m | (ℓ-1)·r ↔ m | d·u·r ↔ n | u·r ↔ n | r` (using `gcd(u,n) = 1`).
But `1 ≤ r < n` implies `n ∤ r`.
-/

namespace ModularSchur

open Finset Nat

variable {m ℓ : ℕ}

/-
Non-multiples of `n = m/gcd(m, ℓ-1)` in `{1, …, m-1}` give ℓ-safe singletons.
-/
theorem singleton_safe_in_stable_range (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m / Nat.gcd m (ℓ - 1)) :
    ((ℓ : ZMod m) - 1) * (r : ZMod m) ≠ 0 := by
  contrapose! hr2;
  refine' Nat.div_le_of_le_mul _;
  -- Since $m$ divides $(ℓ - 1) * r$, we have $m \mid (ℓ - 1) * r$.
  have h_div : m ∣ (ℓ - 1) * r := by
    cases ℓ <;> simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
  rw [ ← Nat.gcd_mul_right ];
  exact Nat.le_of_dvd ( by positivity ) ( Nat.dvd_gcd ( dvd_mul_right _ _ ) h_div )

/-
Corollary: every such singleton is `ℓ`-sum-free in our `IsEllSumFree` sense.
-/
theorem singleton_sumFree_in_stable_range (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < m / Nat.gcd m (ℓ - 1)) :
    IsEllSumFree m ℓ {(r : ZMod m)} := by
  exact ( singleton_sumFree_iff ℓ ( by linarith ) _ ) |>.mpr ( singleton_safe_in_stable_range hm hℓ r hr1 hr2 )

end ModularSchur