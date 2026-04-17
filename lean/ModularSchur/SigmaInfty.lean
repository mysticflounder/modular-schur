import ModularSchur.Basic
import ModularSchur.SingletonSafety

/-!
# Phase 9.1: σ∞(m,c) = m/p(m) when gcd(m, c-1) = 1 — upper bound

The Phase 9.1 upper bound is **purely geometric**: any `C ⊆ ZMod m`
whose pairwise differences are all divisible by some `g | m` with
`g ≥ 2` has `|C| ≤ m/g ≤ m/p(m)`. The `c`-dependence only enters in
the lower bound (not formalized here) via the explicit witness AP
`{1, 1+p, …, 1+(m/p-1)·p}` which is safe iff `p ∤ (c-1)` (which
follows from `gcd(m, c-1) = 1` and `p | m`).

The connection to σ∞: by Phase 8 Theorem 8.1, any stably `c`-safe
subset `C` with `|C| ≥ 2` has its pairwise differences divisible by
some `g | m` with `g ≥ 2` (the "coset step" `g_C`). So the purely
geometric bound `|C| ≤ m/g` applies, and `g ≥ p(m)` gives `|C| ≤ m/p(m)`.
Formalizing Theorem 8.1 itself is deferred.
-/

namespace ModularSchur

open Finset

variable {m : ℕ}

/-
**Coset cardinality bound** (geometric): any `C ⊆ ZMod m` whose
    pairwise differences (as `ℕ` via `.val`) are all divisible by some
    `g | m` with `g ≥ 2` has `|C| ≤ m/g`.

    Proof idea: the function `a ↦ a.val / g` maps `C` into `Fin (m/g)`
    (via divisibility), and is injective on `C` modulo `g`. Since all
    pairs in `C` have `g`-divisible differences, they occupy distinct
    residues mod `g` — which contradicts unless `|C| ≤ m/g`.
-/
theorem card_le_of_pairwise_dvd (m : ℕ) (hm : 2 ≤ m)
    (C : Finset (ZMod m)) (g : ℕ) (hg : g ∣ m) (hg2 : 2 ≤ g)
    (hpair : ∀ a b, a ∈ C → b ∈ C → g ∣ ((b - a : ZMod m).val)) :
    C.card ≤ m / g := by
  -- Quick proof that `#C ≤ m/g` (geometric bound): C is contained in a single residue class `(mod g)`.
  -- Thus `#C ≤ floor((m-1-majorant)/g)+1 ≤ floor((m-1)/g)+1 = m/g`.
  have hC_g_mod : ∃ c : ZMod m, ∀ x ∈ C, x.val % g = c.val % g := by
    obtain h | h := Finset.eq_empty_or_nonempty C;
    · aesop;
    · obtain ⟨ c, hc ⟩ := h;
      use c;
      intro x hx; specialize hpair c x hc hx; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
      cases m <;> simp_all +decide [ ← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add ];
  -- Fix such a residue class `c`.
  obtain ⟨c, hc⟩ := hC_g_mod;
  -- Any element `x ∈ C` can be written as `x = c + kg` for some integer `k`.
  have hC_form : ∀ x ∈ C, ∃ k : ℕ, x.val = c.val % g + k * g ∧ k < m / g := by
    intro x hx;
    have h_bound : x.val < m := by
      haveI := Fact.mk ( by linarith : 1 < m ) ; exact ZMod.val_lt x;
    exact ⟨ x.val / g, by linarith [ Nat.mod_add_div x.val g, hc x hx ], Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_mul_cancel hg ] ⟩;
  have hC_card : C.card ≤ Finset.card (Finset.image (fun k : ℕ => (c.val % g + k * g : ℕ)) (Finset.range (m / g))) := by
    have hC_card : C.card ≤ Finset.card (Finset.image (fun x : ZMod m => x.val) C) := by
      haveI := Fact.mk ( by linarith : 1 < m ) ; rw [ Finset.card_image_of_injective _ fun x y hxy => ZMod.val_injective _ hxy ] ;
    exact hC_card.trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => by obtain ⟨ k, hk₁, hk₂ ⟩ := hC_form x hx; aesop );
  exact hC_card.trans ( Finset.card_image_le.trans ( by simpa ) )

/-
**Phase 9.1 upper bound**: any `C ⊆ ZMod m` whose pairwise
    differences all lie in a proper subgroup of `ZMod m` has
    `|C| ≤ m / p(m)` where `p(m)` is the smallest prime divisor of `m`.
-/
theorem sigmaInfty_le (m : ℕ) (hm : 2 ≤ m)
    (C : Finset (ZMod m))
    (h : ∃ g : ℕ, g ∣ m ∧ 2 ≤ g ∧
           ∀ a b, a ∈ C → b ∈ C → g ∣ ((b - a : ZMod m).val)) :
    C.card ≤ m / m.minFac := by
  obtain ⟨ g, hg₁, hg₂, hg₃ ⟩ := h;
  refine' le_trans ( card_le_of_pairwise_dvd m hm C g hg₁ hg₂ hg₃ ) _;
  gcongr;
  · exact Nat.ne_of_gt ( Nat.minFac_pos _ );
  · exact Nat.minFac_le_of_dvd hg₂ hg₁

end ModularSchur