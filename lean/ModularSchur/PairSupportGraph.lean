/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

module

public import ModularSchur.ResidueAxis

/-!
# Conflict graphs for finite fragment families

This file identifies residue-axis packings with independent sets in the
conflict graph of a finite fragment family. The vertices are the atoms covered
by the fragments, and two distinct vertices are adjacent when some fragment
contains both.

The construction is valid for fragments of arbitrary size. When every
fragment has cardinality two, the fragments themselves are the graph edges,
so the corresponding cover problem is the ordinary edge-cover problem.
-/

@[expose] public section

namespace ModularSchur.PairSupportGraph

open Finset
open ModularSchur.ResidueAxis

variable {α : Type*} [DecidableEq α]

/-- The vertices covered by a finite fragment family. -/
abbrev Support (frags : Finset (Finset α)) := ↥(frags.biUnion id)

/-- Two support vertices conflict when some fragment contains both of them. -/
def conflictGraph (frags : Finset (Finset α)) : SimpleGraph (Support frags) :=
  SimpleGraph.fromRel fun x y => ∃ F ∈ frags, (x : α) ∈ F ∧ (y : α) ∈ F

@[simp] theorem conflictGraph_adj
    (frags : Finset (Finset α)) (x y : Support frags) :
    (conflictGraph frags).Adj x y ↔
      x ≠ y ∧ ∃ F ∈ frags, (x : α) ∈ F ∧ (y : α) ∈ F := by
  rw [conflictGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, h⟩
    · rcases h with ⟨F, hF, hyF, hxF⟩
      exact ⟨hxy, F, hF, hxF, hyF⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, Or.inl h⟩

/-- A packing induces an independent set in the conflict graph. -/
theorem axisPacking_isIndepSet
    {frags : Finset (Finset α)} {P : Finset α}
    (hP : AxisPacking frags P) :
    (conflictGraph frags).IsIndepSet
      (P.subtype (fun x => x ∈ frags.biUnion id)) := by
  intro x hx y hy hxy hAdj
  rw [conflictGraph_adj] at hAdj
  rcases hAdj with ⟨_, F, hF, hxF, hyF⟩
  exact hxy (Subtype.ext (Finset.card_le_one.mp (hP.at_most_one F hF)
    x.1 (Finset.mem_inter.mpr ⟨Finset.mem_subtype.mp hx, hxF⟩)
    y.1 (Finset.mem_inter.mpr ⟨Finset.mem_subtype.mp hy, hyF⟩)))

/-- An independent set in the conflict graph induces an axis packing. -/
theorem isIndepSet_axisPacking
    {frags : Finset (Finset α)} {P : Finset (Support frags)}
    (hP : (conflictGraph frags).IsIndepSet P) :
    AxisPacking frags (P.map (Function.Embedding.subtype _)) := by
  constructor
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  · intro F hF
    apply Finset.card_le_one.mpr
    intro x hx y hy
    rw [Finset.mem_inter] at hx hy
    rcases Finset.mem_map.mp hx.1 with ⟨x', hx'P, hxx'⟩
    rcases Finset.mem_map.mp hy.1 with ⟨y', hy'P, hyy'⟩
    have hxx : x = x'.1 := hxx'.symm
    have hyy : y = y'.1 := hyy'.symm
    subst x
    subst y
    by_contra hxy
    have hxy' : x' ≠ y' := fun h => hxy (congrArg Subtype.val h)
    exact hP hx'P hy'P hxy'
      ((conflictGraph_adj frags x' y').2 ⟨hxy', F, hF, hx.2, hy.2⟩)

/-- A supported atom set is an axis packing precisely when its lift to the
support type is independent in the conflict graph. -/
theorem axisPacking_iff_isIndepSet
    {frags : Finset (Finset α)} {P : Finset α}
    (hPsub : P ⊆ frags.biUnion id) :
    AxisPacking frags P ↔
      (conflictGraph frags).IsIndepSet
        (P.subtype (fun x => x ∈ frags.biUnion id)) := by
  constructor
  · exact axisPacking_isIndepSet
  · intro hP
    have hPacking := isIndepSet_axisPacking hP
    rw [Finset.subtype_map_of_mem hPsub] at hPacking
    exact hPacking

/-- The maximum axis-packing cardinality is the independence number of the
conflict graph. -/
theorem maxPacking_eq_indepNum (frags : Finset (Finset α)) :
    maxPacking frags = (conflictGraph frags).indepNum := by
  classical
  apply le_antisymm
  · have hmem : maxPacking frags ∈ packingCardSet frags := by
      exact Finset.max'_mem _ (packingCardSet_nonempty frags)
    rw [packingCardSet, Finset.mem_filter] at hmem
    rcases hmem.2 with ⟨P, hP, hPcard⟩
    rw [← hPcard]
    have hsubtypeCard :
        (P.subtype (fun x => x ∈ frags.biUnion id)).card = P.card := by
      have hmap := Finset.subtype_map_of_mem
        (p := fun x => x ∈ frags.biUnion id) (s := P) hP.subset_union
      simpa using congrArg Finset.card hmap
    rw [← hsubtypeCard]
    exact (axisPacking_isIndepSet hP).card_le_indepNum
  · obtain ⟨P, hP⟩ :=
      SimpleGraph.exists_isNIndepSet_indepNum (G := conflictGraph frags)
    rw [← hP.card_eq]
    have hcard : (P.map (Function.Embedding.subtype _)).card = P.card := Finset.card_map _
    rw [← hcard]
    exact packing_card_le_maxPacking frags _
      (isIndepSet_axisPacking hP.isIndepSet)

end ModularSchur.PairSupportGraph
