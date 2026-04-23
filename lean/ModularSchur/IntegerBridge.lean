import ModularSchur.Basic
import ModularSchur.Partition

/-!
# Lemma 2.1: Residue reduction (integer ↔ residue bridge)

The paper's Definition 1.1 defines `S_m(k,ℓ)` as the greatest `N` such that the
**integers** `{1,…,N} ⊆ ℕ` admit a `k`-partition into classes whose integer
sums never hit a class member modulo `m`.  The main Lean development
(`Partition.lean`) works on **residues** `{1,…,N} ⊆ ZMod m` via `stableResidues`.
This file defines the integer-level object `schurMod` and proves

    schurMod m k ℓ = schurModResidue m k ℓ       (for 2 ≤ m).

The identification rests on the elementary fact that for `N ≤ m-1` the map
`Nat.cast : ℕ → ZMod m` is injective on `{1,…,N}`, and sum-freeness mod `m`
is preserved under this identification.  This is Lemma 2.1 (residue reduction)
of the paper.
-/

namespace ModularSchur

open Finset

variable {m : ℕ}

/-- Integer-level `ℓ`-sum-freeness mod `m`: for `S ⊆ ℕ`, no `ℓ`-tuple from `S`
    has sum congruent mod `m` to any `y ∈ S`. -/
def IsSumFreeIntMod (m ℓ : ℕ) (S : Finset ℕ) : Prop :=
  ∀ f : Fin ℓ → ℕ, (∀ i, f i ∈ S) → ∀ y ∈ S, (∑ i, f i) % m ≠ y % m

/-- A valid `k`-partition of `{1,…,N} ⊆ ℕ` into `ℓ`-sum-free-mod-`m` classes. -/
structure IsValidPartitionNat (m ℓ k N : ℕ) (P : Fin k → Finset ℕ) : Prop where
  covers   : ∀ x ∈ Finset.Ioc 0 N, ∃ i, x ∈ P i
  disjoint : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  subset   : ∀ i, P i ⊆ Finset.Ioc 0 N
  sumFree  : ∀ i, IsSumFreeIntMod m ℓ (P i)

open Classical in
/-- Integer-level modular Schur number: greatest `N ≤ m-1` such that `{1,…,N}`
    admits a valid `k`-partition into `ℓ`-sum-free-mod-`m` classes.  This is
    the paper's Definition 1.1, with the `N ≤ m-1` cap from Lemma 2.2 baked in. -/
noncomputable def schurMod (m k ℓ : ℕ) : ℕ :=
  Nat.findGreatest
    (fun N => ∃ P : Fin k → Finset ℕ, IsValidPartitionNat m ℓ k N P) (m - 1)

/-- `Nat.findGreatest` only consults its predicate on `[0, n]`; agreement there
    suffices for equality. -/
lemma Nat.findGreatest_congr_aux {P Q : ℕ → Prop}
    [DecidablePred P] [DecidablePred Q] (n : ℕ)
    (h : ∀ k ≤ n, P k ↔ Q k) :
    Nat.findGreatest P n = Nat.findGreatest Q n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hih : Nat.findGreatest P k = Nat.findGreatest Q k :=
      ih (fun j hj => h j (hj.trans (Nat.le_succ k)))
    simp only [Nat.findGreatest_succ]
    by_cases hP : P (k + 1)
    · have hQ : Q (k + 1) := (h (k + 1) le_rfl).mp hP
      rw [if_pos hP, if_pos hQ]
    · have hQ : ¬ Q (k + 1) := fun hQ => hP ((h (k + 1) le_rfl).mpr hQ)
      rw [if_neg hP, if_neg hQ, hih]

/-- The cast `ℕ → ZMod m` is injective on `Ioc 0 (m-1)`. -/
lemma natCast_injOn_Ioc (hm : 2 ≤ m) :
    Set.InjOn ((↑) : ℕ → ZMod m) (Finset.Ioc 0 (m - 1) : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.coe_Ioc, Set.mem_Ioc] at ha hb
  rw [ZMod.natCast_eq_natCast_iff, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega : a < m), Nat.mod_eq_of_lt (by omega : b < m)] at hab
  exact hab

/-- Forward: a valid integer partition of `{1,…,N}` (`N ≤ m-1`) induces a valid
    residue partition of `stableResidues m N`. -/
lemma residue_partition_of_nat (hm : 2 ≤ m) {ℓ k N : ℕ} (hN : N ≤ m - 1)
    {P : Fin k → Finset ℕ} (hP : IsValidPartitionNat m ℓ k N P) :
    ∃ Q : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) Q := by
  refine ⟨fun i => (P i).image ((↑) : ℕ → ZMod m), ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [stableResidues, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨i, hi⟩ := hP.covers a ha
    exact ⟨i, Finset.mem_image.mpr ⟨a, hi, rfl⟩⟩
  · intro i j hij
    rw [Finset.disjoint_iff_ne]
    rintro _ hx _ hy rfl
    simp only [Finset.mem_image] at hx hy
    obtain ⟨a, ha, hac⟩ := hx
    obtain ⟨b, hb, hbc⟩ := hy
    have ha_range : a ∈ Finset.Ioc 0 (m - 1) := by
      have := hP.subset i ha; simp only [Finset.mem_Ioc] at this ⊢; omega
    have hb_range : b ∈ Finset.Ioc 0 (m - 1) := by
      have := hP.subset j hb; simp only [Finset.mem_Ioc] at this ⊢; omega
    have hab : a = b :=
      natCast_injOn_Ioc hm ha_range hb_range (hac.trans hbc.symm)
    subst hab
    exact (Finset.disjoint_iff_ne.mp (hP.disjoint i j hij)) a ha a hb rfl
  · intro i x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact Finset.mem_image.mpr ⟨a, hP.subset i ha, rfl⟩
  · intro i f hf y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨y0, hy0, rfl⟩ := hy
    have : ∀ j : Fin ℓ, ∃ a : ℕ, a ∈ P i ∧ (a : ZMod m) = f j := by
      intro j
      have := hf j
      simp only [Finset.mem_image] at this
      exact this
    choose g hg using this
    have hg_mem : ∀ j, g j ∈ P i := fun j => (hg j).1
    have hg_cast : ∀ j, (g j : ZMod m) = f j := fun j => (hg j).2
    intro hsum
    have hg_sum : (((∑ j, g j) : ℕ) : ZMod m) = ∑ j, f j := by
      push_cast
      exact Finset.sum_congr rfl (fun j _ => hg_cast j)
    have hcast : (((∑ j, g j) : ℕ) : ZMod m) = (y0 : ZMod m) := by
      rw [hg_sum]; exact hsum
    have hmod : (∑ j, g j) % m = y0 % m := by
      rwa [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at hcast
    exact hP.sumFree i g hg_mem y0 hy0 hmod

/-- Backward: a valid residue partition of `stableResidues m N` induces a valid
    integer partition of `{1,…,N}`. -/
lemma nat_partition_of_residue (_hm : 2 ≤ m) {ℓ k N : ℕ} (_hN : N ≤ m - 1)
    {Q : Fin k → Finset (ZMod m)} (hQ : IsValidPartition m ℓ k (stableResidues m N) Q) :
    ∃ P : Fin k → Finset ℕ, IsValidPartitionNat m ℓ k N P := by
  refine ⟨fun i => (Finset.Ioc 0 N).filter (fun a => (a : ZMod m) ∈ Q i), ?_, ?_, ?_, ?_⟩
  · intro a ha
    have ha_img : (a : ZMod m) ∈ stableResidues m N :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := hQ.covers _ ha_img
    exact ⟨i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  · intro i j hij
    rw [Finset.disjoint_filter]
    intro a _ hai haj
    exact (Finset.disjoint_iff_ne.mp (hQ.disjoint i j hij)) _ hai _ haj rfl
  · intro i a ha
    exact (Finset.mem_filter.mp ha).1
  · intro i f hf y hy hsum
    have hf_cast : ∀ j, (f j : ZMod m) ∈ Q i := fun j =>
      (Finset.mem_filter.mp (hf j)).2
    have hy_cast : (y : ZMod m) ∈ Q i := (Finset.mem_filter.mp hy).2
    have hsum_cast : (((∑ j, f j) : ℕ) : ZMod m) = (y : ZMod m) := by
      rw [ZMod.natCast_eq_natCast_iff]; exact hsum
    have hsum' : (∑ j, ((f j : ℕ) : ZMod m)) = (y : ZMod m) := by
      push_cast at hsum_cast; exact hsum_cast
    exact hQ.sumFree i (fun j => (f j : ZMod m)) hf_cast (y : ZMod m) hy_cast hsum'

/-- **Lemma 2.1 (Residue reduction).** For `2 ≤ m`, the integer- and residue-level
    modular Schur numbers agree. -/
theorem schurMod_eq_schurModResidue (m k ℓ : ℕ) (hm : 2 ≤ m) :
    schurMod m k ℓ = schurModResidue m k ℓ := by
  classical
  unfold schurMod schurModResidue
  apply Nat.findGreatest_congr_aux
  intro N hN
  constructor
  · rintro ⟨P, hP⟩; exact residue_partition_of_nat hm hN hP
  · rintro ⟨Q, hQ⟩; exact nat_partition_of_residue hm hN hQ

/-- **Lemma 2.2 (Universal upper bound, integer form).** For `N ≥ m`, no `k`-partition
    of `[1,N]` is `ℓ`-sum-free mod `m`: the element `m ∈ [1,N]` lies in some class `C`,
    and the constant tuple `(m,…,m; m) ∈ C^{ℓ+1}` satisfies `ℓ·m ≡ 0 ≡ m (mod m)`. -/
theorem no_valid_partition_of_ge_m (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : m ≤ N) (P : Fin k → Finset ℕ) (hP : IsValidPartitionNat m ℓ k N P) : False := by
  have hm_mem : m ∈ Finset.Ioc 0 N := by
    simp only [Finset.mem_Ioc]; omega
  obtain ⟨i, hi⟩ := hP.covers m hm_mem
  refine hP.sumFree i (fun _ => m) (fun _ => hi) m hi ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_mod_left, Nat.mod_self]

/-- Consequence: `schurMod m k ℓ` coincides with the unbounded "greatest `N`" of
    Definition 1.1.  Any `N` admitting a valid partition is automatically `≤ m - 1`
    (by `no_valid_partition_of_ge_m`), so the `Nat.findGreatest` cap is lossless. -/
theorem schurMod_is_greatest (hm : 2 ≤ m) {ℓ k N : ℕ}
    (hN : ∃ P, IsValidPartitionNat m ℓ k N P) : N ≤ schurMod m k ℓ := by
  classical
  have hNle : N ≤ m - 1 := by
    by_contra h
    push_neg at h
    obtain ⟨P, hP⟩ := hN
    exact no_valid_partition_of_ge_m hm (by omega) P hP
  exact Nat.le_findGreatest hNle hN

/-- Corollary: the integer-level Schur number satisfies the unified closed form. -/
theorem schurMod_eq (m k ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ)
    (hk : m / Nat.gcd m (ℓ - 1) - 1 ≤ k) :
    schurMod m k ℓ = m / Nat.gcd m (ℓ - 1) - 1 := by
  rw [schurMod_eq_schurModResidue m k ℓ hm, schurModResidue_eq m k ℓ hm hℓ hk]

end ModularSchur
