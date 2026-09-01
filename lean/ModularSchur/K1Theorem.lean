import ModularSchur.Partition

namespace ModularSchur

open Finset Classical

/-!
# k=1 closed form

For 2 ≤ ℓ ≤ m, the single-color-class modular Schur number satisfies
  S_m(1, ℓ) = min(ℓ-1, ⌊m/ℓ⌋).
Resolves D'orville–Sim–Wong–Ho (*Integers* 25, 2025) Problem 1.3.

For m < ℓ, its value is 0 when ℓ ≡ 1 (mod m), and 1 otherwise.

Upper ≤ ℓ-1 (ℓ < m): ℓ ones sum to (ℓ : ZMod m) ∈ stableResidues m N for N ≥ ℓ.
Upper ≤ m/ℓ: for N ≥ m/ℓ+1, some ℓ-tuple in [1,N] sums to m+1 ≡ 1 (mod m).
Lower: nat sums of ℓ elements from [1,N*] lie in [ℓ,m], residues avoid [1,N*] ⊆ [1,ℓ-1].
-/

-- Named predicate so findGreatest_spec can infer P unambiguously.
private def k1Pred (m ℓ : ℕ) : ℕ → Prop :=
  fun N => ∃ P : Fin 1 → Finset (ZMod m), IsValidPartition m ℓ 1 (stableResidues m N) P

/-- For k=1, the single class must equal T, so validity ↔ T is ℓ-sum-free. -/
lemma k1_partition_iff (m ℓ : ℕ) (T : Finset (ZMod m)) :
    (∃ P : Fin 1 → Finset (ZMod m), IsValidPartition m ℓ 1 T P) ↔
    IsEllSumFree m ℓ T := by
  constructor
  · rintro ⟨P, hP⟩
    have hcov : T ⊆ P 0 := by
      intro x hx
      obtain ⟨i, hi⟩ := hP.covers x hx
      have : i = 0 := Subsingleton.elim i 0
      rwa [this] at hi
    have heq : P 0 = T := Finset.Subset.antisymm (hP.subset 0) hcov
    exact heq ▸ hP.sumFree 0
  · intro hT
    exact ⟨fun _ => T, {
      covers   := fun x hx => ⟨0, hx⟩
      disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
      subset   := fun _ => le_refl T
      sumFree  := fun _ => hT }⟩

/-- The trivial all-empty partition witnesses the predicate at N=0. -/
private lemma partition_exists_zero (m ℓ k : ℕ) :
    (fun N => ∃ P : Fin k → Finset (ZMod m),
      IsValidPartition m ℓ k (stableResidues m N) P) 0 := by
  refine ⟨fun _ => ∅, ?_, ?_, ?_, ?_⟩
  · simp [stableResidues]
  · intro i j _; simp
  · intro i; simp
  · intro i; simp [IsEllSumFree]

/-- findGreatest_spec with k1Pred, so the predicate is syntactically manifest. -/
private lemma k1Pred_at_schur (m ℓ : ℕ) : k1Pred m ℓ (schurModResidue m 1 ℓ) :=
  Nat.findGreatest_spec (Nat.zero_le _) (partition_exists_zero m ℓ 1)

/-- For N ≥ ℓ with ℓ < m: ℓ ones sum to ℓ, which lies in stableResidues m N. -/
lemma not_sumFree_of_ge_ell (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlt : ℓ < m) {N : ℕ}
    (hN : ℓ ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  have h1_mem : ∀ _ : Fin ℓ, (1 : ZMod m) ∈ stableResidues m N :=
    fun _ => mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by linarith⟩, by norm_cast⟩
  have hell_mem : (ℓ : ZMod m) ∈ stableResidues m N :=
    mem_image.mpr ⟨ℓ, mem_Ioc.mpr ⟨by linarith, hN⟩, by norm_cast⟩
  have hsum : ∑ _ : Fin ℓ, (1 : ZMod m) = ℓ := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact absurd hsum (h (fun _ => 1) h1_mem ℓ hell_mem)

/-- For N ≥ m/ℓ+1: some ℓ-tuple in [1,N] sums to m+1 ≡ 1 (mod m).
    Construction: q=(m+1)/ℓ, r=(m+1)%ℓ; take r elements = q+1, (ℓ-r) elements = q. -/
lemma not_sumFree_of_ge_quot (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) {N : ℕ}
    (hN : m / ℓ + 1 ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  let q := (m + 1) / ℓ
  let r := (m + 1) % ℓ
  have hq_pos : 1 ≤ q := Nat.div_pos (by linarith) (by linarith)
  have hq_le : q ≤ N := by
    have key : m + 1 ≤ (m / ℓ + 1) * ℓ := by
      have h1 : ℓ * (m / ℓ) + m % ℓ = m := Nat.div_add_mod m ℓ
      have h2 : m % ℓ < ℓ := Nat.mod_lt m (by linarith)
      have eq1 : (m / ℓ + 1) * ℓ = ℓ * (m / ℓ) + ℓ := by ring
      linarith
    show (m + 1) / ℓ ≤ N
    calc (m + 1) / ℓ ≤ (m / ℓ + 1) * ℓ / ℓ := Nat.div_le_div_right key
         _ = m / ℓ + 1 := Nat.mul_div_cancel _ (by linarith)
         _ ≤ N := hN
  let f : Fin ℓ → ZMod m := fun i => if i.val < r then (q + 1 : ℕ) else q
  have hf_mem : ∀ i : Fin ℓ, f i ∈ stableResidues m N := by
    intro i
    simp only [f, stableResidues, mem_image, mem_Ioc]
    split_ifs with hi
    · -- i.val < r, so r > 0, so q * ℓ ≤ m, so q ≤ m/ℓ, so q+1 ≤ m/ℓ+1 ≤ N
      have hr_pos : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
      have hql : q * ℓ ≤ m := by
        have h1 : ℓ * q + r = m + 1 := Nat.div_add_mod (m + 1) ℓ
        have hc : q * ℓ = ℓ * q := mul_comm q ℓ
        linarith
      have hq_le_mq : q ≤ m / ℓ := by
        have h1 : q * ℓ / ℓ ≤ m / ℓ := Nat.div_le_div_right hql
        rwa [Nat.mul_div_cancel _ (by linarith)] at h1
      exact ⟨q + 1, ⟨by omega, by omega⟩, by norm_cast⟩
    · exact ⟨q, ⟨by omega, hq_le⟩, by norm_cast⟩
  have h1_mem : (1 : ZMod m) ∈ stableResidues m N :=
    mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by linarith⟩, by norm_cast⟩
  have hsum : ∑ i : Fin ℓ, f i = (1 : ZMod m) := by
    have hr_lt : r < ℓ := Nat.mod_lt _ (by linarith)
    -- Step 1: compute the nat sum
    have hnat : ∑ i : Fin ℓ, (if i.val < r then q + 1 else q) = m + 1 := by
      simp_rw [show ∀ i : Fin ℓ, (if i.val < r then q + 1 else q) =
          q + (if i.val < r then 1 else 0) from fun i => by split_ifs <;> ring]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                 Fintype.card_fin, smul_eq_mul, Finset.sum_boole]
      have hcard : #{i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} = r := by
        have heq : {i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} =
            Finset.Iio ⟨r, hr_lt⟩ := by
          ext i; simp [Fin.lt_def]
        rw [heq, Fin.card_Iio]
      simp only [hcard, Nat.cast_id]
      exact Nat.div_add_mod (m + 1) ℓ
    -- Step 2: each f i equals (nat_f i : ZMod m)
    have heqi : ∀ i : Fin ℓ, f i = ((if i.val < r then q + 1 else q : ℕ) : ZMod m) :=
      fun i => by simp only [f]; split_ifs <;> norm_cast
    -- Step 3: pull cast outside sum, substitute hnat, reduce (m+1 : ZMod m) = 1
    simp_rw [heqi, ← Nat.cast_sum, hnat]
    rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  exact absurd hsum (h f hf_mem 1 h1_mem)

/-- For N* = min(ℓ-1, m/ℓ): nat sums of ℓ elements from [1,N*] lie in [ℓ,m],
    whose ZMod residues are in {ℓ,…,m-1,0} ∩ {1,…,N*} = ∅. -/
lemma sumFree_min (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    IsEllSumFree m ℓ (stableResidues m (min (ℓ - 1) (m / ℓ))) := by
  set N := min (ℓ - 1) (m / ℓ)
  have hN_le_ell : N ≤ ℓ - 1 := Nat.min_le_left _ _
  have hN_le_quot : N ≤ m / ℓ := Nat.min_le_right _ _
  have hN_lt_m : N < m := by
    calc N ≤ ℓ - 1 := hN_le_ell
         _ ≤ m - 1 := by omega
         _ < m := Nat.sub_lt (by linarith) one_pos
  intro f hf y hy
  have hmem : ∀ i, ∃ n, 1 ≤ n ∧ n ≤ N ∧ (n : ZMod m) = f i := by
    intro i
    simp only [stableResidues, mem_image, mem_Ioc] at hf
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := hf i; exact ⟨n, h1, h2, h3⟩
  obtain ⟨ny, hny_pos, hny_le, hny_cast⟩ : ∃ ny, 1 ≤ ny ∧ ny ≤ N ∧ (ny : ZMod m) = y := by
    simp only [stableResidues, mem_image, mem_Ioc] at hy
    obtain ⟨n, ⟨h1, h2⟩, h3⟩ := hy; exact ⟨n, h1, h2, h3⟩
  choose g hg_pos hg_le hg_cast using hmem
  have hsum_lo : ℓ ≤ ∑ i, g i := by
    calc ℓ = ∑ _i : Fin ℓ, 1 := by simp
         _ ≤ ∑ i : Fin ℓ, g i := Finset.sum_le_sum (fun i _ => hg_pos i)
  have hsum_hi : ∑ i, g i ≤ m := by
    calc ∑ i : Fin ℓ, g i
        ≤ ∑ _i : Fin ℓ, N := Finset.sum_le_sum (fun i _ => hg_le i)
      _ = ℓ * N := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ℓ * (m / ℓ) := Nat.mul_le_mul_left ℓ hN_le_quot
      _ ≤ m := Nat.mul_div_le m ℓ
  have hsum_zmod : (∑ i : Fin ℓ, g i : ZMod m) = ∑ i : Fin ℓ, f i := by
    push_cast
    exact Finset.sum_congr rfl (fun i _ => hg_cast i)
  intro heq
  have hzmod_eq : ((∑ i : Fin ℓ, g i : ℕ) : ZMod m) = (ny : ZMod m) := by
    push_cast; rw [hsum_zmod, heq, hny_cast]
  have hmod : (∑ i : Fin ℓ, g i) % m = ny % m := by
    rwa [ZMod.natCast_eq_natCast_iff, Nat.ModEq] at hzmod_eq
  have hny_lt_m : ny < m := Nat.lt_of_le_of_lt hny_le hN_lt_m
  rw [Nat.mod_eq_of_lt hny_lt_m] at hmod
  rcases Nat.lt_or_eq_of_le hsum_hi with hlt | heqm
  · rw [Nat.mod_eq_of_lt hlt] at hmod; omega
  · rw [← heqm, Nat.mod_self] at hmod; omega

/-- **D'orville Problem 1.3 (resolved).**
    For 2 ≤ ℓ ≤ m, the single-class modular Schur number is min(ℓ-1, ⌊m/ℓ⌋). -/
theorem schurModResidue_k1 (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) (hlm : ℓ ≤ m) :
    schurModResidue m 1 ℓ = min (ℓ - 1) (m / ℓ) := by
  apply le_antisymm
  · rw [Nat.le_min]
    refine ⟨?_, ?_⟩
    · -- Upper bound ≤ ℓ-1
      rcases Nat.eq_or_lt_of_le hlm with rfl | hlt
      · exact Nat.findGreatest_le _  -- ℓ = m: trivially ≤ m-1 = ℓ-1
      · -- ℓ < m: if schurModResidue ≥ ℓ, extract violation at that N
        by_contra hc; push_neg at hc
        have hge : ℓ ≤ schurModResidue m 1 ℓ := by omega
        have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
          (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
        exact not_sumFree_of_ge_ell hm hℓ hlt hge hspec
    · -- Upper bound ≤ m/ℓ: if schurModResidue > m/ℓ, extract violation
      by_contra hc; push_neg at hc
      have hge : m / ℓ + 1 ≤ schurModResidue m 1 ℓ := by omega
      have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
        (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
      exact not_sumFree_of_ge_quot hm hℓ hlm hge hspec
  · -- Lower bound: min(ℓ-1, m/ℓ) is achievable
    apply Nat.le_findGreatest
    · have hlt : m / ℓ < m := Nat.div_lt_self (by linarith) (by linarith)
      calc min (ℓ - 1) (m / ℓ) ≤ m / ℓ := Nat.min_le_right _ _
           _ ≤ m - 1 := by omega
    · rw [k1_partition_iff]; exact sumFree_min hm hℓ hlm

/-- If `ℓ ≡ 1 (mod m)`, the all-ones `ℓ`-tuple obstructs every nonempty interval. -/
private lemma not_sumFree_stableResidues_of_mod_eq_one (m ℓ : ℕ) (hmod : ℓ % m = 1)
    {N : ℕ} (hN : 1 ≤ N) : ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  have h1_mem : ∀ _ : Fin ℓ, (1 : ZMod m) ∈ stableResidues m N :=
    fun _ => mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, hN⟩, by norm_cast⟩
  have hsum : ∑ _ : Fin ℓ, (1 : ZMod m) = 1 := by
    rw [show ∑ _ : Fin ℓ, (1 : ZMod m) = (ℓ : ZMod m) by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]]
    rw [← ZMod.natCast_mod ℓ m, hmod]
    norm_num
  have h1_target : (1 : ZMod m) ∈ stableResidues m N :=
    mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, hN⟩, by norm_cast⟩
  exact absurd hsum (h (fun _ => 1) h1_mem 1 h1_target)

/-- If `ℓ ≢ 1 (mod m)`, the singleton interval is `ℓ`-sum-free. -/
private lemma sumFree_stableResidues_one_of_mod_ne_one (m ℓ : ℕ) (hm : 2 ≤ m)
    (hmod : ℓ % m ≠ 1) : IsEllSumFree m ℓ (stableResidues m 1) := by
  intro f hf y hy
  have hf_eq : ∀ i, f i = (1 : ZMod m) := by
    intro i
    simp [stableResidues] at hf
    exact hf i
  have hy_eq : y = (1 : ZMod m) := by
    simpa [stableResidues] using hy
  intro heq
  have hcast : (ℓ : ZMod m) = (1 : ZMod m) := by
    simpa [hf_eq, hy_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using heq
  have hmod_eq : ℓ % m = 1 % m :=
    (ZMod.natCast_eq_natCast_iff' ℓ 1 m).mp (by simpa using hcast)
  rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at hmod_eq
  exact hmod hmod_eq

/-- When `m < ℓ`, the residue interval through `2` is never `ℓ`-sum-free. -/
private lemma not_sumFree_stableResidues_of_two_le_of_modulus_lt (m ℓ : ℕ)
    (hm : 2 ≤ m) (hml : m < ℓ) {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsEllSumFree m ℓ (stableResidues m N) := by
  intro h
  by_cases hmod : ℓ % m = 1
  · exact not_sumFree_stableResidues_of_mod_eq_one m ℓ hmod (by omega) h
  · let a := ℓ % m
    let r := if a = 0 then 1 else m + 1 - a
    have ha_lt : a < m := Nat.mod_lt _ (by omega)
    have ha_ne_one : a ≠ 1 := by simpa [a] using hmod
    have hr_pos : 1 ≤ r := by
      dsimp [r]
      split_ifs <;> omega
    have hr_lt_m : r < m := by
      dsimp [r]
      split_ifs <;> omega
    have hr_lt_ell : r < ℓ := lt_trans hr_lt_m hml
    let f : Fin ℓ → ZMod m := fun i => if i.val < r then 2 else 1
    have hf_mem : ∀ i, f i ∈ stableResidues m N := by
      intro i
      simp only [f]
      split_ifs
      · exact mem_image.mpr ⟨2, mem_Ioc.mpr ⟨by omega, hN⟩, by norm_cast⟩
      · exact mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by omega⟩, by norm_cast⟩
    have hnat : ∑ i : Fin ℓ, (if i.val < r then 2 else 1) = ℓ + r := by
      simp_rw [show ∀ i : Fin ℓ, (if i.val < r then 2 else 1) =
          1 + (if i.val < r then 1 else 0) from fun i => by split_ifs <;> omega]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, Finset.sum_boole]
      have hcard : #{i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} = r := by
        have heq : {i ∈ (Finset.univ : Finset (Fin ℓ)) | i.val < r} =
            Finset.Iio ⟨r, hr_lt_ell⟩ := by
          ext i
          simp [Fin.lt_def]
        rw [heq, Fin.card_Iio]
      simp only [hcard, Nat.cast_id]
      omega
    have hsum_mod : (ℓ + r) % m = 1 := by
      by_cases ha : a = 0
      · have hr : r = 1 := by simp [r, ha]
        have hell_mod : ℓ % m = 0 := by simpa [a] using ha
        rw [hr, Nat.add_mod, hell_mod]
        simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
      · have hr : r = m + 1 - a := by simp [r, ha]
        have hsum : a + r = m + 1 := by omega
        rw [Nat.add_mod, show ℓ % m = a by rfl, Nat.mod_eq_of_lt hr_lt_m, hsum]
        simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
    have hsum : ∑ i : Fin ℓ, f i = (1 : ZMod m) := by
      have heqi : ∀ i : Fin ℓ, f i = ((if i.val < r then 2 else 1 : ℕ) : ZMod m) :=
        fun i => by simp only [f]; split_ifs <;> norm_cast
      simp_rw [heqi, ← Nat.cast_sum, hnat, ← ZMod.natCast_mod (ℓ + r) m, hsum_mod]
      norm_num
    have h1_mem : (1 : ZMod m) ∈ stableResidues m N :=
      mem_image.mpr ⟨1, mem_Ioc.mpr ⟨one_pos, by omega⟩, by norm_cast⟩
    exact absurd hsum (h f hf_mem 1 h1_mem)

/-- For `m < ℓ`, the one-color value records whether the singleton interval is
    `ℓ`-sum-free. -/
theorem schurModResidue_k1_of_modulus_lt (m ℓ : ℕ) (hm : 2 ≤ m) (hml : m < ℓ) :
    schurModResidue m 1 ℓ = if ℓ % m = 1 then 0 else 1 := by
  split_ifs with hmod
  · apply Nat.eq_zero_of_le_zero
    by_contra hpos
    have hge : 1 ≤ schurModResidue m 1 ℓ := by omega
    have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
      (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
    exact not_sumFree_stableResidues_of_mod_eq_one m ℓ hmod hge hspec
  · apply le_antisymm
    · by_contra hc
      have hge : 2 ≤ schurModResidue m 1 ℓ := by omega
      have hspec : IsEllSumFree m ℓ (stableResidues m (schurModResidue m 1 ℓ)) :=
        (k1_partition_iff m ℓ _).mp (k1Pred_at_schur m ℓ)
      exact not_sumFree_stableResidues_of_two_le_of_modulus_lt m ℓ hm hml hge hspec
    · apply Nat.le_findGreatest
      · omega
      · rw [k1_partition_iff]
        exact sumFree_stableResidues_one_of_mod_ne_one m ℓ hm hmod

/-- Complete one-color formula for every `m ≥ 2` and `ℓ ≥ 2`. -/
theorem schurModResidue_k1_all (m ℓ : ℕ) (hm : 2 ≤ m) (hℓ : 2 ≤ ℓ) :
    schurModResidue m 1 ℓ =
      if ℓ ≤ m then min (ℓ - 1) (m / ℓ) else if ℓ % m = 1 then 0 else 1 := by
  by_cases hlm : ℓ ≤ m
  · rw [if_pos hlm]
    exact schurModResidue_k1 m ℓ hm hℓ hlm
  · rw [if_neg hlm]
    exact schurModResidue_k1_of_modulus_lt m ℓ hm (by omega)

end ModularSchur
