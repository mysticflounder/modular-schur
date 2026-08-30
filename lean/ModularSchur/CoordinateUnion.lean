import ModularSchur.TauClosure

/-!
# Coordinate-union edge rule

This file records the black-box version of the coordinate-union edge rule used
by the residue-coordinate DP line of work.

The theorem is intentionally stated at the level of a finite fragment family
`F : ι → Finset α` with an explicit coordinate map `rho`.  The atom-level
quotient lift is now in place via the atom-class restatement below and the
same-support fiber API in `SameSupportFiber.lean`; the PID use-site theorem is
formalized separately in `WholeAxisPID.lean`.
-/

namespace ModularSchur.CoordinateUnion

open ModularSchur.TauClosure
open Finset

section

variable {α ι : Type*} [DecidableEq α] [Fintype ι]

/-- The set of labels of fragments containing `x`. -/
def supportLabels (label : ι → ℕ) (F : ι → Finset α) (x : α) : Finset ℕ :=
  (Finset.univ.filter (fun i => x ∈ F i)).image label

/-- The fragment graph: two points are adjacent when they co-occur in some fragment. -/
def adjacent (F : ι → Finset α) (x y : α) : Prop :=
  ∃ i, x ∈ F i ∧ y ∈ F i

/-- Membership in the support-label set is exactly the existence of a witness
fragment with that label. -/
theorem mem_supportLabels_iff (label : ι → ℕ) (F : ι → Finset α) (x : α) (g : ℕ) :
    g ∈ supportLabels label F x ↔ ∃ i, label i = g ∧ x ∈ F i := by
  constructor
  · intro hg
    unfold supportLabels at hg
    rcases Finset.mem_image.mp hg with ⟨i, hi, rfl⟩
    refine ⟨i, rfl, ?_⟩
    simpa using (Finset.mem_filter.mp hi).2
  · rintro ⟨i, rfl, hx⟩
    unfold supportLabels
    exact Finset.mem_image.mpr ⟨i, by simp [hx], rfl⟩

/-- Support labels are invariant under atom equivalence. -/
theorem supportLabels_congr {label : ι → ℕ} {F : ι → Finset α} {x y : α}
    (h : atomEquiv F x y) :
    supportLabels label F x = supportLabels label F y := by
  ext g
  constructor
  · intro hg
    rcases (mem_supportLabels_iff label F x g).1 hg with ⟨i, hgi, hxF⟩
    exact (mem_supportLabels_iff label F y g).2
      ⟨i, hgi, (mem_fragment_of_atomEquiv F h i).1 hxF⟩
  · intro hg
    rcases (mem_supportLabels_iff label F y g).1 hg with ⟨i, hgi, hyF⟩
    exact (mem_supportLabels_iff label F x g).2
      ⟨i, hgi, (mem_fragment_of_atomEquiv F h i).2 hyF⟩

/-- Adjacency is invariant under atom equivalence in each coordinate. -/
theorem adjacent_congr {F : ι → Finset α} {x x' y y' : α}
    (hx : atomEquiv F x x') (hy : atomEquiv F y y') :
    adjacent F x y ↔ adjacent F x' y' := by
  constructor
  · intro hxy
    rcases hxy with ⟨i, hxF, hyF⟩
    exact ⟨i, (mem_fragment_of_atomEquiv F hx i).1 hxF,
              (mem_fragment_of_atomEquiv F hy i).1 hyF⟩
  · intro hxy
    rcases hxy with ⟨i, hxF, hyF⟩
    exact ⟨i, (mem_fragment_of_atomEquiv F hx i).2 hxF,
              (mem_fragment_of_atomEquiv F hy i).2 hyF⟩

/-- Support labels on atoms, defined by quotienting out `atomEquiv`. -/
def atomSupportLabels (label : ι → ℕ) (F : ι → Finset α) :
    AtomClass F → Finset ℕ :=
  Quotient.lift (supportLabels label F)
    (fun x y h => supportLabels_congr (label := label) (F := F) h)

/-- The atom-level adjacency relation induced by fragment co-occurrence. -/
def atomAdjacent (F : ι → Finset α) : AtomClass F → AtomClass F → Prop :=
  fun x y =>
    Quotient.liftOn₂ x y (fun a b => adjacent F a b)
      (by
        intro a₁ b₁ a₂ b₂ ha hb
        exact propext (adjacent_congr (F := F) ha hb))

/-- Quotient support labels agree with the pointwise support labels. -/
theorem atomSupportLabels_mk (label : ι → ℕ) (F : ι → Finset α) (x : α) :
    atomSupportLabels label F (atomClass F x) = supportLabels label F x := rfl

/-- Quotient adjacency agrees with pointwise adjacency. -/
theorem atomAdjacent_mk (F : ι → Finset α) (x y : α) :
    atomAdjacent F (atomClass F x) (atomClass F y) ↔ adjacent F x y := by
  rfl

/-- Coordinate-union edge rule, pointwise form.

If membership in a fragment is detected by the coordinate map `rho` and the
fragment's label-specific residue, then on any fixed support fiber adjacency is
equivalent to equality on some support coordinate.
-/
theorem coordinateUnionEdgeRule
    (label : ι → ℕ) (F : ι → Finset α)
    (rho : ℕ → α → ℕ) (residue : ι → ℕ)
    (hNF : ∀ i x, x ∈ F i ↔ rho (label i) x = residue i)
    {P : Finset ℕ} {x y : α}
    (hx : supportLabels label F x = P) (_hy : supportLabels label F y = P) :
    adjacent F x y ↔ ∃ g ∈ P, rho g x = rho g y := by
  constructor
  · intro hxy
    rcases hxy with ⟨i, hxF, hyF⟩
    have hg : label i ∈ P := by
      rw [← hx]
      exact (mem_supportLabels_iff label F x (label i)).2 ⟨i, rfl, hxF⟩
    refine ⟨label i, hg, ?_⟩
    have hxr : rho (label i) x = residue i := (hNF i x).1 hxF
    have hyr : rho (label i) y = residue i := (hNF i y).1 hyF
    exact hxr.trans hyr.symm
  · rintro ⟨g, hgP, hxy⟩
    have hgx : g ∈ supportLabels label F x := by
      rw [hx]
      exact hgP
    rcases (mem_supportLabels_iff label F x g).1 hgx with ⟨i, hgi, hxF⟩
    have hxr : rho g x = residue i := by
      simpa [hgi] using (hNF i x).1 hxF
    have hyr : rho g y = residue i := by
      exact hxy.symm.trans hxr
    have hyr' : rho (label i) y = residue i := by
      simpa [hgi] using hyr
    have hyF : y ∈ F i := by
      exact (hNF i y).2 hyr'
    exact ⟨i, hxF, hyF⟩

/-- The induced fiber graph is a union of coordinate cliques. -/
theorem coordinateCliqueUnion
    (label : ι → ℕ) (F : ι → Finset α)
    (rho : ℕ → α → ℕ) (residue : ι → ℕ)
    (hNF : ∀ i x, x ∈ F i ↔ rho (label i) x = residue i)
    {P : Finset ℕ} {x y : α}
    (hx : supportLabels label F x = P) (hy : supportLabels label F y = P) :
    adjacent F x y ↔ ∃ g ∈ P, rho g x = rho g y :=
  coordinateUnionEdgeRule label F rho residue hNF hx hy

/-- Atom-class form of the coordinate-union edge rule.

This is the quotient-level restatement obtained by applying the pointwise
theorem to representatives and transporting it through `atomClass`.
-/
theorem coordinateUnionEdgeRule_atomClass
    (label : ι → ℕ) (F : ι → Finset α)
    (rho : ℕ → α → ℕ) (residue : ι → ℕ)
    (hNF : ∀ i x, x ∈ F i ↔ rho (label i) x = residue i)
    {P : Finset ℕ} {x y : α}
    (hx : atomSupportLabels label F (atomClass F x) = P)
    (hy : atomSupportLabels label F (atomClass F y) = P) :
    atomAdjacent F (atomClass F x) (atomClass F y) ↔ ∃ g ∈ P, rho g x = rho g y := by
  simpa [atomSupportLabels_mk, atomAdjacent_mk] using
    (coordinateUnionEdgeRule (label := label) (F := F) (rho := rho) (residue := residue)
      hNF
      (x := x) (y := y)
      (by simpa [atomSupportLabels_mk] using hx)
      (by simpa [atomSupportLabels_mk] using hy))

end

end ModularSchur.CoordinateUnion
