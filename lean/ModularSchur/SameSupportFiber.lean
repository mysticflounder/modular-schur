import ModularSchur.CoordinateUnion

/-!
# Same-support fibers

This file packages the atom-class coordinate-union edge rule in the language of
same-support fibers `X_P` and a minimal cell API.

It now constructs the canonical `rho_g` quotient lift from abstract residue
data. The scanner-side `rho_respects` hypothesis is materialized by generated
normalized-cell bridge files built from concrete scanner data.
-/

namespace ModularSchur.SameSupportFiber

open ModularSchur.TauClosure
open ModularSchur.CoordinateUnion
open Finset

/-! ## Cell API -/

/-- Minimal same-support cell API.

This bundles the fragment family, the pointwise residue map, and the
well-definedness proof needed to quotient it to atoms.
-/
structure SameSupportCell (α ι : Type*) [DecidableEq α] where
  label : ι → ℕ
  F : ι → Finset α
  rho : ℕ → α → ℕ
  residue : ι → ℕ
  hNF : ∀ i x, x ∈ F i ↔ rho (label i) x = residue i
  rho_respects : ∀ g x y, atomEquiv F x y → rho g x = rho g y

variable {α ι : Type*} [DecidableEq α]

namespace SameSupportCell

/-- The canonical atom-level coordinate map, obtained by quotienting the
pointwise residue function. -/
noncomputable def rho_g (cell : SameSupportCell α ι) (g : ℕ) : AtomClass cell.F → ℕ :=
  Quotient.lift (fun x : α => cell.rho g x)
    (by
      intro x y h
      exact cell.rho_respects g x y h)

@[simp] theorem rho_g_mk (cell : SameSupportCell α ι) (g : ℕ) (x : α) :
    rho_g cell g (atomClass cell.F x) = cell.rho g x := by
  rfl

end SameSupportCell

/-- Scanner-facing alias for the same-support cell API.

This keeps the current Lean surface aligned with the proof notes, which speak
about normalized cells. The concrete scanner-side instantiation is supplied by
generated bridge files.
-/
abbrev NormalizedCell (α ι : Type*) [DecidableEq α] := SameSupportCell α ι

/-- If a concrete scanner family already separates atoms by their membership
signatures, then any pointwise coordinate map respects atom equivalence
automatically.

This is the helper used by the generated seven-cell bridge files: they prove
the concrete atom signatures are injective, then reuse this lemma to populate
`rho_respects` on the corresponding `NormalizedCell` records.
-/
theorem rho_respects_of_atomEquiv_eq
    (F : ι → Finset α) {rho : ℕ → α → ℕ}
    (hEq : ∀ x y, atomEquiv F x y → x = y) :
    ∀ g x y, atomEquiv F x y → rho g x = rho g y := by
  intro g x y h
  exact congrArg (rho g) (hEq x y h)

/-- Build a concrete same-support cell from a pointwise family and an
atom-signature injectivity proof.  Generated scanner-side bridge files use
this helper to keep the `NormalizedCell` packaging uniform. -/
def of_atomEquiv_eq
    (label : ι → ℕ) (F : ι → Finset α) {rho : ℕ → α → ℕ}
    (residue : ι → ℕ)
    (hNF : ∀ i x, x ∈ F i ↔ rho (label i) x = residue i)
    (hEq : ∀ x y, atomEquiv F x y → x = y) : SameSupportCell α ι :=
  { label := label,
    F := F,
    rho := rho,
    residue := residue,
    hNF := hNF,
    rho_respects := rho_respects_of_atomEquiv_eq F (rho := rho) hEq }

section

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]

/-- The same-support fiber `X_P` of atoms whose support pattern is exactly `P`. -/
def X_P (label : ι → ℕ) (F : ι → Finset α) [Fintype (AtomClass F)]
    (P : Finset ℕ) : Finset (AtomClass F) :=
  Finset.univ.filter (fun A => atomSupportLabels label F A = P)

/-- Membership in `X_P` is exactly equality of support pattern with `P`. -/
theorem mem_X_P_iff (label : ι → ℕ) (F : ι → Finset α) [Fintype (AtomClass F)]
    (P : Finset ℕ)
    (A : AtomClass F) :
    A ∈ X_P label F P ↔ atomSupportLabels label F A = P := by
  simp [X_P]

/-- `rho_g` is the `g`-coordinate of a residue coordinate family.

This is a point-level notation layer for the proof notes.  The atom-level
quotient coordinate already exists: `SameSupportCell.rho_g` (above), the
`Quotient.lift` of `cell.rho g` along `cell.rho_respects`, with `rho_g_mk` as its
computation rule.  Downstream consumers use that one.
-/
abbrev rho_g (rho : ℕ → α → ℕ) (g : ℕ) : α → ℕ :=
  rho g

/-- Fiber-level form of the coordinate-union edge rule.

The theorem packages the already-proved atom-class restatement in the language
of the same-support fiber `X_P`.
-/
theorem coordinateUnionEdgeRule_on_X_P
    (label : ι → ℕ) (F : ι → Finset α)
    [Fintype (AtomClass F)]
    (rho : ℕ → α → ℕ) (residue : ι → ℕ)
    (hNF : ∀ i x, x ∈ F i ↔ rho (label i) x = residue i)
    {P : Finset ℕ} {x y : α}
    (hx : atomClass F x ∈ X_P label F P)
    (hy : atomClass F y ∈ X_P label F P) :
    atomAdjacent F (atomClass F x) (atomClass F y) ↔ ∃ g ∈ P, rho_g rho g x = rho_g rho g y := by
  simpa [X_P, rho_g] using
    (coordinateUnionEdgeRule_atomClass (label := label) (F := F)
      (rho := rho) (residue := residue) (hNF := hNF)
      (P := P) (x := x) (y := y)
      ((mem_X_P_iff (label := label) (F := F) (P := P) (A := atomClass F x)).1 hx)
      ((mem_X_P_iff (label := label) (F := F) (P := P) (A := atomClass F y)).1 hy))

/-- AtomClass-level form of the coordinate-union edge rule for a cell API. -/
theorem coordinateUnionEdgeRule_on_cell
    (cell : SameSupportCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} {A B : AtomClass cell.F}
    (hA : A ∈ X_P cell.label cell.F P)
    (hB : B ∈ X_P cell.label cell.F P) :
    atomAdjacent cell.F A B ↔ ∃ g ∈ P, SameSupportCell.rho_g cell g A = SameSupportCell.rho_g cell g B := by
  rcases Quotient.exists_rep A with ⟨x, rfl⟩
  rcases Quotient.exists_rep B with ⟨y, rfl⟩
  have h :=
    coordinateUnionEdgeRule_on_X_P
      (label := cell.label) (F := cell.F) (rho := cell.rho)
      (residue := cell.residue) (hNF := cell.hNF)
      (P := P) (x := x) (y := y) hA hB
  simpa [X_P, SameSupportCell.rho_g] using h

/-- Normalized-cell restatement of the same-support fiber theorem. -/
theorem coordinateUnionEdgeRule_on_normalizedCell
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} {A B : AtomClass cell.F}
    (hA : A ∈ X_P cell.label cell.F P)
    (hB : B ∈ X_P cell.label cell.F P) :
    atomAdjacent cell.F A B ↔ ∃ g ∈ P, SameSupportCell.rho_g cell g A = SameSupportCell.rho_g cell g B := by
  simpa using (coordinateUnionEdgeRule_on_cell (cell := cell) (P := P) (A := A) (B := B) hA hB)

end

end ModularSchur.SameSupportFiber
