import ModularSchur.SameSupportFiber
import ModularSchur.ResidueAxis
import ModularSchur.AnchoredExactTransversal

/-!
# Whole-axis PID theorems

Projection-injective dominance (PID) on an axis `h` says `rho_g h` is
injective on the same-support fiber `X_P`.

`axis_cover_eq_card_of_PID` proves exactness for the SINGLE-AXIS fragment
family `axis_h_frags` under PID on that axis.  It does not bound the cover
number of the full coordinate-clique family `coordCliques`: PID on one axis
is not sufficient there, and that stronger reading (Theorem A of
`docs/proofs/whole-axis-sufficient-conditions.md`) is refuted by explicit
fibers (`docs/proofs/wap-sufficiency-refutation-2026-08-23.md`).

`axis_cover_coordCliques_eq_card_of_forall_PID` is the corrected full-family
statement: under PID on EVERY axis of `P` (a separated fiber, which by the
Coordinate-Union Edge Rule has no atom-graph edges) the axis cover of
`coordCliques` equals the fiber cardinality.
`axis_cover_coordCliques_eq_card_of_singleton_pattern` specializes to
`|P| = 1`, where NF2 provides the injectivity (`PID_of_singleton_pattern`).
-/

namespace ModularSchur.WholeAxisPID

open Classical
open Finset
open ModularSchur.AnchoredExactTransversal
open ModularSchur.CoordinateUnion
open ModularSchur.ResidueAxis
open ModularSchur.SameSupportFiber
open ModularSchur.TauClosure

universe u v

variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

/-- Projection-injective dominance on axis `h`. -/
def PID (cell : SameSupportCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) (h : ℕ) : Prop :=
  Set.InjOn (SameSupportCell.rho_g cell h) (X_P cell.label cell.F P)

/-- The set of atoms in `X_P` with h-coordinate `r`. -/
noncomputable def axisClique (cell : SameSupportCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) (h r : ℕ) :
    Finset (AtomClass cell.F) := by
  classical
  exact (X_P cell.label cell.F P).filter (fun A => SameSupportCell.rho_g cell h A = r)

/-- The h-axis fragment family. -/
noncomputable def axis_h_frags (cell : SameSupportCell α ι)
    [Fintype (AtomClass cell.F)] (P : Finset ℕ) (h : ℕ) :
    Finset (Finset (AtomClass cell.F)) := by
  classical
  exact (pi_h (X_P cell.label cell.F P) (SameSupportCell.rho_g cell) h).image
    (axisClique cell P h)

/-- Occupied axis cliques are injective on occupied residues. -/
theorem axisClique_injOn (cell : SameSupportCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) (h : ℕ) :
    Set.InjOn (axisClique cell P h)
      (pi_h (X_P cell.label cell.F P) (SameSupportCell.rho_g cell) h) := by
  classical
  intro r hr1 r' hr2 hEq
  rcases Finset.mem_image.mp hr1 with ⟨A, hA, hAr⟩
  have hA' : A ∈ axisClique cell P h r' := by
    have hmem : (A ∈ axisClique cell P h r) = (A ∈ axisClique cell P h r') := by
      exact congrArg (fun S => A ∈ S) hEq
    have hAaxis : A ∈ axisClique cell P h r := by
      simp [axisClique, hA, hAr]
    exact hmem.mp hAaxis
  have hAr' : SameSupportCell.rho_g cell h A = r' := by
    exact (Finset.mem_filter.mp hA').2
  exact hAr.symm.trans hAr'

/-- The h-axis cover family covers `X_P`. -/
theorem wholeAxisCover_of_PID (cell : SameSupportCell α ι)
    [Fintype (AtomClass cell.F)] {P : Finset ℕ} {h : ℕ}
    :
    WholeAxisCover (axis_h_frags cell P h) (X_P cell.label cell.F P)
      (SameSupportCell.rho_g cell) h (axis_h_frags cell P h) := by
  classical
  refine ⟨?sub, ?fiber, ?cover, ?card⟩
  · exact subset_rfl
  · intro A hA
    rcases Finset.mem_biUnion.mp hA with ⟨F, hF, hAF⟩
    rw [axis_h_frags] at hF
    rcases Finset.mem_image.mp hF with ⟨r, hr, rfl⟩
    exact (Finset.mem_filter.mp hAF).1
  · intro A hA
    apply Finset.mem_biUnion.mpr
    refine ⟨axisClique cell P h (SameSupportCell.rho_g cell h A), ?_, ?_⟩
    · rw [axis_h_frags]
      exact Finset.mem_image.mpr
        ⟨SameSupportCell.rho_g cell h A,
          Finset.mem_image.mpr ⟨A, hA, rfl⟩,
          rfl⟩
    · simp [axisClique, hA]
  · rw [axis_h_frags]
    rw [Finset.card_image_iff]
    exact axisClique_injOn cell P h

/-- The h-axis packing: the whole fiber itself. -/
theorem axisPacking_of_PID (cell : SameSupportCell α ι)
    [Fintype (AtomClass cell.F)] {P : Finset ℕ} {h : ℕ}
    (hPID : PID cell P h) :
    AxisPacking (axis_h_frags cell P h) (X_P cell.label cell.F P) := by
  classical
  refine ⟨?subset_union, ?at_most_one⟩
  · intro A hA
    apply Finset.mem_biUnion.mpr
    refine ⟨axisClique cell P h (SameSupportCell.rho_g cell h A), ?_, ?_⟩
    · rw [axis_h_frags]
      exact Finset.mem_image.mpr
        ⟨SameSupportCell.rho_g cell h A,
          Finset.mem_image.mpr ⟨A, hA, rfl⟩,
          rfl⟩
    · simp [axisClique, hA]
  · intro F hF
    rw [axis_h_frags] at hF
    rcases Finset.mem_image.mp hF with ⟨r, hr, rfl⟩
    rw [Finset.card_le_one]
    intro A hA B hB
    rcases Finset.mem_inter.mp hA with ⟨hAX, hAF⟩
    rcases Finset.mem_inter.mp hB with ⟨hBX, hBF⟩
    have hAr : SameSupportCell.rho_g cell h A = r := by
      exact (Finset.mem_filter.mp hAF).2
    have hBr : SameSupportCell.rho_g cell h B = r := by
      exact (Finset.mem_filter.mp hBF).2
    exact hPID hAX hBX (hAr.trans hBr.symm)

/-- The axis-cover exactness theorem under PID. -/
theorem axis_cover_eq_card_of_PID (cell : SameSupportCell α ι)
    [Fintype (AtomClass cell.F)] {P : Finset ℕ} {h : ℕ}
    (hPID : PID cell P h) :
    axis_cover (axis_h_frags cell P h) = (X_P cell.label cell.F P).card := by
  classical
  have hPcard : (X_P cell.label cell.F P).card =
      (pi_h (X_P cell.label cell.F P) (SameSupportCell.rho_g cell) h).card := by
    simpa [ResidueAxis.pi_h] using (Finset.card_image_iff.2 hPID).symm
  simpa [hPcard] using axis_cover_eq_projection_card_of_wholeAxis
    (wholeAxisCover_of_PID cell)
    (axisPacking_of_PID cell hPID)
    hPcard

/-- The singleton-pattern corollary: a one-element support fiber is
projection-injective on its unique axis. -/
theorem PID_of_singleton_pattern (cell : SameSupportCell α ι)
    [Fintype α] [Fintype (AtomClass cell.F)] {P : Finset ℕ}
    (hP : P.card = 1) :
    ∃ h ∈ P, PID cell P h := by
  obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hP
  refine ⟨g, by simp, ?_⟩
  intro A hA B hB hρ
  rcases Quotient.exists_rep A with ⟨x, rfl⟩
  rcases Quotient.exists_rep B with ⟨y, rfl⟩
  have hAx : supportLabels cell.label cell.F x = ({g} : Finset ℕ) := by
    simpa [atomSupportLabels_mk] using
      (mem_X_P_iff (label := cell.label) (F := cell.F) (P := ({g} : Finset ℕ))
        (A := atomClass cell.F x)).1 hA
  have hBx : supportLabels cell.label cell.F y = ({g} : Finset ℕ) := by
    simpa [atomSupportLabels_mk] using
      (mem_X_P_iff (label := cell.label) (F := cell.F) (P := ({g} : Finset ℕ))
        (A := atomClass cell.F y)).1 hB
  have hAdj : atomAdjacent cell.F (atomClass cell.F x) (atomClass cell.F y) := by
    exact (coordinateUnionEdgeRule_on_cell (cell := cell) (P := ({g} : Finset ℕ))
      (A := atomClass cell.F x) (B := atomClass cell.F y) hA hB).2 ⟨g, by simp, hρ⟩
  have hxy : adjacent cell.F x y := (atomAdjacent_mk (F := cell.F) (x := x) (y := y)).1 hAdj
  rcases hxy with ⟨i, hxF, hyF⟩
  have hi : cell.label i = g := by
    have hmem : cell.label i ∈ ({g} : Finset ℕ) := by
      rw [← hAx]
      exact (mem_supportLabels_iff (label := cell.label) (F := cell.F) (x := x)
        (g := cell.label i)).2 ⟨i, rfl, hxF⟩
    simpa using hmem
  apply (atomClass_eq_iff (cell.F) x y).2
  unfold atomEquiv signature
  funext j
  by_cases hj : cell.label j = g
  · have hiff : x ∈ cell.F j ↔ y ∈ cell.F j := by
      constructor
      · intro hxj
        have hxgi : cell.rho g x = cell.residue i := by
          simpa [hi] using (cell.hNF i x).1 hxF
        have hxgj : cell.rho g x = cell.residue j := by
          simpa [hj] using (cell.hNF j x).1 hxj
        have hres : cell.residue i = cell.residue j := hxgi.symm.trans hxgj
        have hygi : cell.rho g y = cell.residue i := by
          simpa [hi] using (cell.hNF i y).1 hyF
        have hygj : cell.rho g y = cell.residue j := by
          exact hygi.trans hres
        exact (cell.hNF j y).2 (by simpa [hj] using hygj)
      · intro hyj
        have hxi : cell.rho g x = cell.residue i := by
          simpa [hi] using (cell.hNF i x).1 hxF
        have hygi : cell.rho g y = cell.residue i := by
          simpa [hi] using (cell.hNF i y).1 hyF
        have hygj : cell.rho g y = cell.residue j := by
          simpa [hj] using (cell.hNF j y).1 hyj
        have hres : cell.residue i = cell.residue j := hygi.symm.trans hygj
        have hxi' : cell.rho g x = cell.residue j := by
          exact hxi.trans hres
        exact (cell.hNF j x).2 (by simpa [hj] using hxi')
    simpa [signature] using congrArg (fun p : Prop => decide p) (propext hiff)
  · have hx_not : x ∉ cell.F j := by
      intro hxj
      have hjmem : cell.label j = g := by
        have hmem : cell.label j ∈ ({g} : Finset ℕ) := by
          rw [← hAx]
          exact (mem_supportLabels_iff (label := cell.label) (F := cell.F) (x := x)
            (g := cell.label j)).2 ⟨j, rfl, hxj⟩
        simpa using hmem
      exact hj hjmem
    have hy_not : y ∉ cell.F j := by
      intro hyj
      have hjmem : cell.label j = g := by
        have hmem : cell.label j ∈ ({g} : Finset ℕ) := by
          rw [← hBx]
          exact (mem_supportLabels_iff (label := cell.label) (F := cell.F) (x := y)
            (g := cell.label j)).2 ⟨j, rfl, hyj⟩
        simpa using hmem
      exact hj hjmem
    have hiff : x ∈ cell.F j ↔ y ∈ cell.F j := by
      constructor <;> intro h
      · exact False.elim (hx_not h)
      · exact False.elim (hy_not h)
    simpa [signature] using congrArg (fun p : Prop => decide p) (propext hiff)

/-- The single-axis fragment slice and the coordinate clique at the same
axis and residue are the same finite set. -/
theorem coordClique_eq_axisClique (cell : SameSupportCell α ι)
    [Fintype (AtomClass cell.F)] (P : Finset ℕ) (h r : ℕ) :
    coordClique cell P h r = axisClique cell P h r := by
  ext A
  simp [coordClique, axisClique]

/-- Any single axis of the pattern slices the fiber into a subfamily of the
full coordinate-clique family. -/
theorem axis_h_frags_subset_coordCliques (cell : SameSupportCell α ι)
    [Fintype (AtomClass cell.F)] {P : Finset ℕ} {h : ℕ} (hh : h ∈ P) :
    axis_h_frags cell P h ⊆ coordCliques cell P := by
  classical
  intro C hC
  rw [axis_h_frags] at hC
  rcases Finset.mem_image.mp hC with ⟨r, hr, rfl⟩
  unfold coordCliques
  exact Finset.mem_biUnion.mpr
    ⟨h, hh, Finset.mem_image.mpr ⟨r, hr, coordClique_eq_axisClique cell P h r⟩⟩

/-- Sufficiency over the FULL coordinate-clique family: if every axis of the
pattern is projection-injective on the fiber (a separated fiber, edgeless in
the atom graph by the Coordinate-Union Edge Rule), the axis cover of
`coordCliques` equals the fiber cardinality.  Injectivity on one axis alone
does not give this; see `docs/proofs/wap-sufficiency-refutation-2026-08-23.md`. -/
theorem axis_cover_coordCliques_eq_card_of_forall_PID
    (cell : SameSupportCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} {h : ℕ} (hh : h ∈ P)
    (hsep : ∀ g ∈ P, PID cell P g) :
    axis_cover (coordCliques cell P) = (X_P cell.label cell.F P).card := by
  classical
  have hW := wholeAxisCover_of_PID (cell := cell) (P := P) (h := h)
  have hCov : IsCoverOf (coordCliques cell P) (axis_h_frags cell P h) := by
    refine ⟨axis_h_frags_subset_coordCliques cell hh, ?_⟩
    intro A hA
    rcases Finset.mem_biUnion.mp hA with ⟨C, hC, hAC⟩
    exact hW.covers_fiber (coordCliques_subset_X_P cell P C hC hAC)
  have hPack : AxisPacking (coordCliques cell P) (X_P cell.label cell.F P) := by
    refine ⟨?_, ?_⟩
    · intro A hA
      refine Finset.mem_biUnion.mpr
        ⟨coordClique cell P h (SameSupportCell.rho_g cell h A), ?_, ?_⟩
      · exact coordClique_mem_coordCliques_of_class_witness cell P hh hA rfl
      · simp [coordClique, hA]
    · exact independent_of_axis_injective cell
        (fun g hg A hA B hB hne hEq => hne (hsep g hg hA hB hEq))
  have hcard : (axis_h_frags cell P h).card = (X_P cell.label cell.F P).card := by
    have hproj : (X_P cell.label cell.F P).card =
        (pi_h (X_P cell.label cell.F P) (SameSupportCell.rho_g cell) h).card := by
      simpa [ResidueAxis.pi_h] using (Finset.card_image_iff.2 (hsep h hh)).symm
    rw [hW.card_eq_projection, hproj]
  calc axis_cover (coordCliques cell P)
      = (axis_h_frags cell P h).card :=
        axis_cover_eq_card_of_cover_and_packing hCov hPack hcard
    _ = (X_P cell.label cell.F P).card := hcard

/-- The `|P| = 1` corollary over the FULL coordinate-clique family: on a
singleton support pattern the unique axis is projection-injective (NF2), and
it is the only axis, so the full family's axis cover equals the fiber
cardinality unconditionally. -/
theorem axis_cover_coordCliques_eq_card_of_singleton_pattern
    (cell : SameSupportCell α ι) [Fintype α] [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (hP : P.card = 1) :
    axis_cover (coordCliques cell P) = (X_P cell.label cell.F P).card := by
  obtain ⟨g, rfl⟩ := Finset.card_eq_one.mp hP
  obtain ⟨h, hh, hPID⟩ := PID_of_singleton_pattern cell (Finset.card_singleton g)
  have hg : h = g := Finset.mem_singleton.mp hh
  refine axis_cover_coordCliques_eq_card_of_forall_PID cell
    (Finset.mem_singleton_self g) ?_
  intro g' hg'
  have hgg : g' = g := Finset.mem_singleton.mp hg'
  subst hgg
  exact hg ▸ hPID

end ModularSchur.WholeAxisPID
