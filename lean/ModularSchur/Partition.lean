import ModularSchur.Basic
import ModularSchur.SingletonSafety
import ModularSchur.UniversalBound
import ModularSchur.UnifiedValue
import ModularSchur.UnifiedTheorem
import ModularSchur.StableRange

/-!
# Modular Schur number `S_m(k,ℓ)` — partition framework

Direct definition: `S_m(k,ℓ)` is the greatest `N` such that `{1,…,N} ⊆ ℕ`
admits a `k`-partition into subsets that are `ℓ`-sum-free modulo `m`.

Equivalently, working in residues: `{1,…,N}` mapped into `ZMod m` via `Nat.cast`
admits a `k`-partition into `ℓ`-sum-free classes of `ZMod m`.

This file defines the object and states the main unified theorem.
-/

namespace ModularSchur

open Finset

variable {m : ℕ}

/-- A valid `k`-partition of a residue set `T ⊆ ZMod m` into `ℓ`-sum-free classes. -/
structure IsValidPartition (m ℓ k : ℕ) (T : Finset (ZMod m))
    (P : Fin k → Finset (ZMod m)) : Prop where
  covers     : ∀ x ∈ T, ∃ i, x ∈ P i
  disjoint   : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  subset     : ∀ i, P i ⊆ T
  sumFree    : ∀ i, IsEllSumFree m ℓ (P i)

/-- The residue set of `{1,…,N}` in `ZMod m`. -/
def stableResidues (m N : ℕ) : Finset (ZMod m) :=
  (Finset.Ioc 0 N).image ((↑) : ℕ → ZMod m)

open Classical in
/-- `schurModResidue m k ℓ` = greatest `N` such that `stableResidues m N` admits
    a valid `k`-partition, bounded above by `m - 1` per Lemma 1.2. -/
noncomputable def schurModResidue (m k ℓ : ℕ) : ℕ :=
  Nat.findGreatest
    (fun N => ∃ P : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) P) (m - 1)

/-
**Phase 7 unified theorem — upper bound (partition level).** If `N ≥ m/gcd(m,ℓ-1)`
    then `stableResidues m N` admits no `ℓ`-sum-free `k`-partition: the class containing
    `(n : ZMod m)` (where `n = m/gcd(m,ℓ-1)`) cannot be `ℓ`-sum-free by `class_containing_n_not_sumFree`.
-/
theorem schurModResidue_le (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurModResidue m k ℓ ≤ m / Nat.gcd m (ℓ - 1) - 1 := by
  -- By contradiction, assume that $n \leq \text{schurModResidue } m k \ell$.
  by_contra h_contra;
  obtain ⟨N, hN⟩ : ∃ N, N = schurModResidue m k ℓ ∧ N ≥ m / Nat.gcd m (ℓ - 1) ∧ ∃ P : Fin k → Finset (ZMod m), IsValidPartition m ℓ k (stableResidues m N) P := by
    refine' ⟨ _, rfl, _, _ ⟩;
    · exact Nat.le_of_pred_lt ( not_le.mp h_contra );
    · apply Classical.byContradiction
      intro h_no_partition;
      convert Nat.findGreatest_eq_iff.mp _;
      rotate_left;
      exact schurModResidue m k ℓ;
      exact m - 1;
      use fun N => ∃ P : Fin k → Finset ( ZMod m ), IsValidPartition m ℓ k ( stableResidues m N ) P;
      exact?;
      · rfl;
      · grind;
  obtain ⟨ hN₁, hN₂, P, hP ⟩ := hN; have := hP.covers ( ( m / Nat.gcd m ( ℓ - 1 ) : ℕ ) : ZMod m ) ; simp_all +decide ;
  obtain ⟨ i, hi ⟩ := this ( Finset.mem_image.mpr ⟨ m / m.gcd ( ℓ - 1 ), Finset.mem_Ioc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( Nat.gcd_dvd_left _ _ ) ) ( Nat.gcd_pos_of_pos_left _ ( by linarith ) ), by linarith ⟩, rfl ⟩ ) ; exact class_containing_n_not_sumFree hm hℓ _ hi ( hP.sumFree i ) ;

/-
**Phase 7 unified theorem — lower bound (partition level).** If `k ≥ m/gcd(m,ℓ-1) - 1`,
    then `stableResidues m (m/gcd(m,ℓ-1) - 1)` admits the all-singletons partition.
-/
theorem le_schurModResidue (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    m / Nat.gcd m (ℓ - 1) - 1 ≤ schurModResidue m k ℓ := by
  -- Let $n = m / \gcd(m, \ell - 1)$.
  set n := m / Nat.gcd m (ℓ - 1);
  apply_rules [ Nat.le_findGreatest ];
  · exact Nat.sub_le_sub_right ( Nat.div_le_self _ _ ) _;
  · -- Define the partition P as follows:
    -- For each i in Fin k, if i.val < n - 1, then P i is the singleton set containing (i.val + 1) in ZMod m.
    -- Otherwise, P i is the empty set.
    use fun i => if i.val < n - 1 then {(↑(i.val + 1) : ZMod m)} else ∅;
    constructor <;> norm_num;
    · intro x hx; unfold stableResidues at hx; simp_all +decide [ Fin.exists_iff ] ;
      obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := hx; use a - 1; rcases a with ( _ | a ) <;> simp_all +decide ; omega;
    · intro i j hij; split_ifs <;> simp_all +decide [ Fin.ext_iff, Set.disjoint_left ] ;
      rw [ ZMod.natCast_eq_natCast_iff ];
      rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> contrapose! hij <;> linarith [ Nat.div_le_self m ( Nat.gcd m ( ℓ - 1 ) ), Nat.sub_add_cancel ( show 1 ≤ m / Nat.gcd m ( ℓ - 1 ) from Nat.div_pos ( Nat.le_of_dvd ( by linarith ) ( Nat.gcd_dvd_left _ _ ) ) ( Nat.gcd_pos_of_pos_left _ ( by linarith ) ) ) ];
    · intro i; split_ifs <;> simp +decide [ *, stableResidues ] ;
      exact ⟨ i + 1, ⟨ Nat.succ_pos _, by linarith ⟩, by norm_cast ⟩;
    · intro i; split_ifs <;> simp_all +decide [ IsEllSumFree ] ;
      intro f hf; have := singleton_sumFree_in_stable_range hm hℓ ( i + 1 ) ( by linarith ) ( by omega ) ; simp_all +decide [ IsEllSumFree ] ;

/-- **Phase 7 Unified Theorem.** For `k ≥ m/gcd(m,ℓ-1) - 1`,
    `schurModResidue m k ℓ = m/gcd(m,ℓ-1) - 1`. -/
theorem schurModResidue_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    schurModResidue m k ℓ = m / Nat.gcd m (ℓ - 1) - 1 :=
  le_antisymm (schurModResidue_le m k ℓ hm hℓ) (le_schurModResidue m k ℓ hm hℓ hk)

end ModularSchur