import ModularSchur.Basic

/-!
# Tau Closure — Ingredient 1: Canonical Atomization

Let `F(d₀) = {F₁, …, Fₛ}` be the maximal residual fragments of a normalized
cell `d₀` after private forcing.  Define the canonical atomization of the
residual point set `R(d₀)` as the partition induced by joint membership
pattern across all fragments:

    x ~ y  ↔  (∀ i, x ∈ Fᵢ ↔ y ∈ Fᵢ).

The equivalence classes (atoms) are the coarsest partition of `R(d₀)` for
which every fragment is a union of parts.

## Main results

* `atomEquiv` — the equivalence relation on residual points.
* `AtomClass` — the type of atoms (equivalence classes).
* `mem_fragment_of_atomEquiv` — every fragment is a union of atoms.
* `signatureQuot_injective` — `|A| ≤ 2^s` (atoms inject into `ι → Bool`).
* `atomization_is_coarsest` — the atom partition is the coarsest such partition.
* `ingredient1` — bundles the three key properties.

We work in a type-agnostic setting: `α` is the type of residual points,
`ι` indexes the fragments, and `F : ι → Finset α` gives the fragment family.
-/

namespace ModularSchur.TauClosure

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α ι : Type*} [DecidableEq α] [Fintype ι]

/-! ## The membership-pattern equivalence -/

/-- The membership signature of `x`: which fragments contain `x`. -/
def signature (F : ι → Finset α) (x : α) : ι → Bool :=
  fun i => decide (x ∈ F i)

/-- Two residual points are **atom-equivalent** iff they have the same
    membership signature across all fragments. -/
def atomEquiv (F : ι → Finset α) (x y : α) : Prop :=
  signature F x = signature F y

-- `abbrev` makes this setoid transparent so `Quotient.sound`/`exact` see through it.
private abbrev atomSetoid (F : ι → Finset α) : Setoid α where
  r     := atomEquiv F
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-! ## Atoms -/

/-- The **atom set**: equivalence classes under `atomEquiv`. -/
abbrev AtomClass (F : ι → Finset α) := Quotient (atomSetoid F)

/-- The canonical projection `α → AtomClass F`. -/
abbrev atomClass (F : ι → Finset α) : α → AtomClass F :=
  Quotient.mk (atomSetoid F)

theorem atomClass_eq_iff (F : ι → Finset α) (x y : α) :
    atomClass F x = atomClass F y ↔ atomEquiv F x y := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-! ## Membership criterion in terms of atoms -/

/-- Membership in fragment `i` depends only on the atom class:
    if `x ~ y` then `x ∈ F i ↔ y ∈ F i`. -/
theorem mem_fragment_of_atomEquiv (F : ι → Finset α) {x y : α}
    (h : atomEquiv F x y) (i : ι) : x ∈ F i ↔ y ∈ F i := by
  have hx : decide (x ∈ F i) = decide (y ∈ F i) := congr_fun h i
  constructor
  · intro hxi
    have h' : decide (x ∈ F i) = true := decide_eq_true_eq.mpr hxi
    exact decide_eq_true_eq.mp (hx ▸ h')
  · intro hyi
    have h' : decide (y ∈ F i) = true := decide_eq_true_eq.mpr hyi
    exact decide_eq_true_eq.mp (hx.symm ▸ h')

/-! ## Cardinality bound: |A| ≤ 2^|ι| via signature injection -/

/-- The signature map factors through `AtomClass F`. -/
def signatureQuot (F : ι → Finset α) : AtomClass F → (ι → Bool) :=
  Quotient.lift (signature F) (fun _ _ h => h)

/-- The quotient signature map is injective, so `|A| ≤ |ι → Bool| = 2^|ι|`. -/
theorem signatureQuot_injective (F : ι → Finset α) :
    Function.Injective (signatureQuot F) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  exact Quotient.sound hab

/-! ## Every fragment is a union of atoms -/

/-- **Ingredient 1, Part 2**: every fragment `F i` is a union of atoms. -/
theorem fragment_is_union_of_atoms (F : ι → Finset α) (i : ι) :
    ∀ x y : α, atomEquiv F x y → (x ∈ F i ↔ y ∈ F i) :=
  fun _x _y h => mem_fragment_of_atomEquiv F h i

/-! ## Coarseness: atom partition is the coarsest making fragments unions -/

/-- A partition `π : α → β` **respects** the fragment family `F` if every
    fragment is a union of `π`-fibers. -/
def Respects (F : ι → Finset α) {β : Type*} (π : α → β) : Prop :=
  ∀ x y, π x = π y → ∀ i, x ∈ F i ↔ y ∈ F i

/-- **Ingredient 1, coarsestness.**  The atom partition is coarsest: any `π`
    that respects `F` coarsens to it.  Note this is a standalone result — it is
    *not* one of the three conjuncts of `ingredient1` below, and is not carried
    by `tau_capstone`. -/
theorem atomization_is_coarsest (F : ι → Finset α) {β : Type*} (π : α → β)
    (hπ : Respects F π) : ∀ x y, π x = π y → atomClass F x = atomClass F y := by
  intro x y hxy
  apply Quotient.sound
  funext i
  have h_iff : x ∈ F i ↔ y ∈ F i := hπ x y hxy i
  simp only [signature, h_iff]

/-! ## Summary -/

/-- **Ingredient 1 (Canonical Atomization).**

    For any fragment family `F : ι → Finset α`:
    1. Membership in each `F i` is constant on atom-equivalence classes.
    2. The atom map injects into `ι → Bool`, giving `|A| ≤ 2^|ι|`.
    3. `atomClass` is exactly atom-equivalence: `atomClass F x = atomClass F y`
       iff `atomEquiv F x y`.

    Coarsestness of the atom partition is the separate `atomization_is_coarsest`
    above; it is deliberately not bundled here. -/
theorem ingredient1 (F : ι → Finset α) :
    (∀ i x y, atomEquiv F x y → (x ∈ F i ↔ y ∈ F i)) ∧
    (Function.Injective (signatureQuot F)) ∧
    (∀ x y, atomClass F x = atomClass F y ↔ atomEquiv F x y) :=
  ⟨fun i x y h => mem_fragment_of_atomEquiv F h i,
   signatureQuot_injective F,
   atomClass_eq_iff F⟩

/-! ## Ingredient 2a: Signature-Tree Decomposition

Given a signature map `σ : α → (ι → Bool)`, the partial-signature trie gives a
tree-decomposition blueprint for the atom graph `G_atom`.  Nodes are partial
signatures `p : ι → Option Bool`; the bag at `p` is every atom whose full
signature extends `p`.

* `compatible` / `sigBag` — compatibility predicate and bag function.
* `SigRefines` — refinement partial order (`p` refines `q` means `p` is at least as
  constrained).
* `sigBag_antitone` — finer signature → smaller bag.
* `mem_sigBag_iff` — `x ∈ sigBag σ p` iff `fullPartialSig σ x` refines `p`.
* `sigLCA` — LCA (join) of two partial signatures.
* `SigRefines_left/right` — LCA is coarser than each input.
* `sigBag_covers_pair` — edge coverage: every pair co-occurs in their LCA bag.
* `sigBag_subtree` — subtree / path property required for a tree decomposition.
* `ingredient2a` — bundles all four properties.
-/

/-- A **partial signature** over index type `ι`:
    `some b` constrains coordinate `i` to value `b`; `none` leaves it free. -/
def PartialSig (ι : Type*) := ι → Option Bool

/-- Atom `x` is **compatible** with partial signature `p` under signature map `σ`:
    every constrained coordinate of `p` agrees with `σ x`. -/
def compatible (σ : α → ι → Bool) (p : PartialSig ι) (x : α) : Prop :=
  ∀ i b, p i = some b → σ x i = b

/-- The **signature bag** at `p`: all atoms compatible with `p`. -/
def sigBag (σ : α → ι → Bool) (p : PartialSig ι) : Set α :=
  {x | compatible σ p x}

/-- `p` **refines** `q` when every constraint of `q` is also a constraint of `p`
    (so `p` is at least as restrictive). -/
def SigRefines (p q : PartialSig ι) : Prop :=
  ∀ i b, q i = some b → p i = some b

/-- **Anti-monotonicity of bags**: a more-constrained partial signature has a
    smaller bag. -/
theorem sigBag_antitone (σ : α → ι → Bool) {p q : PartialSig ι}
    (h : SigRefines p q) : sigBag σ p ⊆ sigBag σ q := by
  intro x hx i b hqi
  exact hx i b (h i b hqi)

/-- The **full partial signature** of atom `x`: every coordinate is constrained
    to the value given by `σ x`. -/
def fullPartialSig (σ : α → ι → Bool) (x : α) : PartialSig ι :=
  fun i => some (σ x i)

/-- Every atom lies in the bag of its own full partial signature. -/
theorem mem_sigBag_fullPartialSig (σ : α → ι → Bool) (x : α) :
    x ∈ sigBag σ (fullPartialSig σ x) := by
  intro i b h
  simp only [fullPartialSig] at h
  exact Option.some.inj h

/-- `x ∈ sigBag σ p` iff the full signature of `x` refines `p`. -/
theorem mem_sigBag_iff (σ : α → ι → Bool) (p : PartialSig ι) (x : α) :
    x ∈ sigBag σ p ↔ SigRefines (fullPartialSig σ x) p := by
  simp only [sigBag, Set.mem_setOf_eq, compatible, SigRefines, fullPartialSig]
  constructor
  · intro h i b hpi; exact congrArg some (h i b hpi)
  · intro h i b hpi; exact Option.some.inj (h i b hpi)

/-- The **LCA** of two partial signatures: constrained to `b` at `i` iff both
    inputs agree on `b`; unconstrained wherever they differ. -/
def sigLCA (p q : PartialSig ι) : PartialSig ι :=
  fun i => if p i = q i then p i else none

/-- `p` refines its LCA with `q` (the LCA is coarser than `p`). -/
theorem SigRefines_left (p q : PartialSig ι) : SigRefines p (sigLCA p q) := by
  intro i b h
  unfold sigLCA at h
  by_cases heq : p i = q i
  · rwa [if_pos heq] at h
  · simp [if_neg heq] at h

/-- `q` refines its LCA with `p` (the LCA is coarser than `q`). -/
theorem SigRefines_right (p q : PartialSig ι) : SigRefines q (sigLCA p q) := by
  intro i b h
  unfold sigLCA at h
  by_cases heq : p i = q i
  · rw [if_pos heq] at h; rwa [← heq]
  · simp [if_neg heq] at h

/-- `sigLCA` is commutative. -/
theorem sigLCA_comm (p q : PartialSig ι) : sigLCA p q = sigLCA q p := by
  funext i; unfold sigLCA
  by_cases h : p i = q i
  · rw [if_pos h, if_pos h.symm]; exact h
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- If atom `x` lies in bag `p`, it also lies in the LCA of `p` with any other
    partial signature (bags only grow as we go to a coarser node). -/
theorem mem_sigBag_lca_of_mem_left (σ : α → ι → Bool) {p q : PartialSig ι} {x : α}
    (hp : x ∈ sigBag σ p) : x ∈ sigBag σ (sigLCA p q) :=
  sigBag_antitone σ (SigRefines_left p q) hp

/-- **Covering property**: every pair of atoms co-occurs in their LCA bag.
    This establishes the edge-coverage condition for `G_atom`. -/
theorem sigBag_covers_pair (σ : α → ι → Bool) (x y : α) :
    x ∈ sigBag σ (sigLCA (fullPartialSig σ x) (fullPartialSig σ y)) ∧
    y ∈ sigBag σ (sigLCA (fullPartialSig σ x) (fullPartialSig σ y)) :=
  ⟨sigBag_antitone σ (SigRefines_left _ _) (mem_sigBag_fullPartialSig σ x),
   sigBag_antitone σ (SigRefines_right _ _) (mem_sigBag_fullPartialSig σ y)⟩

/-- **Subtree property**: an atom in two bags lies in their LCA bag.
    This is the path / interval condition required for a valid tree decomposition. -/
theorem sigBag_subtree (σ : α → ι → Bool) {p q : PartialSig ι} {x : α}
    (hp : x ∈ sigBag σ p) (_hq : x ∈ sigBag σ q) :
    x ∈ sigBag σ (sigLCA p q) :=
  mem_sigBag_lca_of_mem_left σ hp

/-! ## Summary of Ingredient 2a -/

/-- **Ingredient 2a (Signature-Tree Decomposition).**

    For any signature map `σ : α → (ι → Bool)`, the partial-signature family
    `{sigBag σ p | p : PartialSig ι}` is a valid tree-decomposition blueprint:

    1. **Self-membership**: every atom lies in its own full-signature bag.
    2. **Anti-monotonicity**: finer signature → smaller bag (connectedness condition).
    3. **Pair coverage**: every pair of atoms co-occurs in their LCA bag (edge coverage).
    4. **Subtree property**: any atom in two bags also lies in their LCA bag. -/
theorem ingredient2a (σ : α → ι → Bool) :
    (∀ x : α, x ∈ sigBag σ (fullPartialSig σ x)) ∧
    (∀ (p q : PartialSig ι), SigRefines p q → sigBag σ p ⊆ sigBag σ q) ∧
    (∀ x y : α,
        x ∈ sigBag σ (sigLCA (fullPartialSig σ x) (fullPartialSig σ y)) ∧
        y ∈ sigBag σ (sigLCA (fullPartialSig σ x) (fullPartialSig σ y))) ∧
    (∀ (p q : PartialSig ι) (x : α),
        x ∈ sigBag σ p → x ∈ sigBag σ q → x ∈ sigBag σ (sigLCA p q)) :=
  ⟨mem_sigBag_fullPartialSig σ,
   fun _p _q h => sigBag_antitone σ h,
   fun x y => sigBag_covers_pair σ x y,
   fun _p _q _x hp _hq => mem_sigBag_lca_of_mem_left σ hp⟩

/-! ## Ingredient 2b: Three-Rail Bag Decomposition and Bag-Size Bound

Given a coordinate assignment `ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁` (the canonical
`ρ`-normal form from the scan), the **frontier bag** at node `u` decomposes into:

- `bagAnchor ρ u` — atoms at exactly `u` (size ≤ 1 by injectivity)
- `bagRail2/5/11 ρ u` — atoms strictly above `u` in each coordinate (size ≤ `nₚ`)

**2bA**: the four parts are pairwise disjoint.
**2bB + counting**: `|frontierBag ρ u| ≤ 1 + n₂ + n₅ + n₁₁`.
Specializing to `n₂ = 8, n₅ = 4, n₁₁ = 3` gives `|frontierBag ρ u| ≤ 16`
and hence `tw(G_atom(d₀)) ≤ 15` on the `n = 220` ray. -/

section ThreeRailDecomposition

variable {β : Type*} [DecidableEq β] [Fintype β] {n₂ n₅ n₁₁ : ℕ}

/-- Atoms at exactly `u` (the anchor). -/
def bagAnchor (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u : Fin n₂ × Fin n₅ × Fin n₁₁) : Finset β :=
  Finset.univ.filter (fun a => ρ a = u)

/-- Atoms strictly above `u` in the 2-coordinate, fixed at `u` in the others. -/
def bagRail2 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u : Fin n₂ × Fin n₅ × Fin n₁₁) : Finset β :=
  Finset.univ.filter (fun a => u.1 < (ρ a).1 ∧ (ρ a).2 = u.2)

/-- Atoms strictly above `u` in the 5-coordinate, fixed at `u` in the others. -/
def bagRail5 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u : Fin n₂ × Fin n₅ × Fin n₁₁) : Finset β :=
  Finset.univ.filter (fun a => u.2.1 < (ρ a).2.1 ∧ (ρ a).1 = u.1 ∧ (ρ a).2.2 = u.2.2)

/-- Atoms strictly above `u` in the 11-coordinate, fixed at `u` in the others. -/
def bagRail11 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u : Fin n₂ × Fin n₅ × Fin n₁₁) : Finset β :=
  Finset.univ.filter (fun a => u.2.2 < (ρ a).2.2 ∧ (ρ a).1 = u.1 ∧ (ρ a).2.1 = u.2.1)

/-- The full frontier bag: anchor plus three rails. -/
def frontierBag (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u : Fin n₂ × Fin n₅ × Fin n₁₁) : Finset β :=
  bagAnchor ρ u ∪ bagRail2 ρ u ∪ bagRail5 ρ u ∪ bagRail11 ρ u

/-! ### 2bA: pairwise disjointness -/

theorem bagAnchor_disjoint_rail2 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁) (u) :
    Disjoint (bagAnchor ρ u) (bagRail2 ρ u) := by
  simp only [Finset.disjoint_left, bagAnchor, bagRail2, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rintro a ha ⟨hlt, -⟩
  rw [ha] at hlt; exact absurd hlt (lt_irrefl _)

theorem bagAnchor_disjoint_rail5 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁) (u) :
    Disjoint (bagAnchor ρ u) (bagRail5 ρ u) := by
  simp only [Finset.disjoint_left, bagAnchor, bagRail5, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rintro a ha ⟨hlt, -⟩
  rw [ha] at hlt; exact absurd hlt (lt_irrefl _)

theorem bagAnchor_disjoint_rail11 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁) (u) :
    Disjoint (bagAnchor ρ u) (bagRail11 ρ u) := by
  simp only [Finset.disjoint_left, bagAnchor, bagRail11, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rintro a ha ⟨hlt, -⟩
  rw [ha] at hlt; exact absurd hlt (lt_irrefl _)

theorem bagRail2_disjoint_rail5 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁) (u) :
    Disjoint (bagRail2 ρ u) (bagRail5 ρ u) := by
  simp only [Finset.disjoint_left, bagRail2, bagRail5, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rintro a ⟨-, heq⟩ ⟨hlt, -⟩
  rw [congr_arg Prod.fst heq] at hlt; exact absurd hlt (lt_irrefl _)

theorem bagRail2_disjoint_rail11 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁) (u) :
    Disjoint (bagRail2 ρ u) (bagRail11 ρ u) := by
  simp only [Finset.disjoint_left, bagRail2, bagRail11, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rintro a ⟨-, heq⟩ ⟨hlt, -⟩
  rw [congr_arg Prod.snd heq] at hlt; exact absurd hlt (lt_irrefl _)

theorem bagRail5_disjoint_rail11 (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁) (u) :
    Disjoint (bagRail5 ρ u) (bagRail11 ρ u) := by
  simp only [Finset.disjoint_left, bagRail5, bagRail11, Finset.mem_filter,
             Finset.mem_univ, true_and]
  rintro a ⟨hlt, -, -⟩ ⟨-, -, h4⟩
  rw [h4] at hlt; exact absurd hlt (lt_irrefl _)

/-! ### 2bB: size bounds under rail-wise injectivity -/

theorem bagAnchor_card_le_one (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u) (hρ : Set.InjOn ρ (bagAnchor ρ u)) : (bagAnchor ρ u).card ≤ 1 :=
  Finset.card_le_one.mpr fun a ha b hb => by
    have ha' := ha
    have hb' := hb
    simp only [bagAnchor, Finset.mem_filter, Finset.mem_univ, true_and] at ha' hb'
    exact hρ ha hb (ha'.trans hb'.symm)

private lemma injOn_rail {γ : Type*} [DecidableEq γ] [Fintype γ] {m : ℕ}
    {ρ : γ → Fin m} {s : Finset γ} (hρ : Set.InjOn ρ ↑s) :
    s.card ≤ m :=
  calc s.card = (Finset.image ρ s).card := (Finset.card_image_of_injOn hρ).symm
    _ ≤ Fintype.card (Fin m) := Finset.card_le_univ _
    _ = m := Fintype.card_fin m

theorem bagRail2_card_le (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u) (hρ : Set.InjOn (fun a => (ρ a).1) (bagRail2 ρ u)) : (bagRail2 ρ u).card ≤ n₂ :=
  injOn_rail (s := bagRail2 ρ u) (ρ := fun a => (ρ a).1) hρ

theorem bagRail5_card_le (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u) (hρ : Set.InjOn (fun a => (ρ a).2.1) (bagRail5 ρ u)) : (bagRail5 ρ u).card ≤ n₅ :=
  injOn_rail (s := bagRail5 ρ u) (ρ := fun a => (ρ a).2.1) hρ

theorem bagRail11_card_le (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (u) (hρ : Set.InjOn (fun a => (ρ a).2.2) (bagRail11 ρ u)) : (bagRail11 ρ u).card ≤ n₁₁ :=
  injOn_rail (s := bagRail11 ρ u) (ρ := fun a => (ρ a).2.2) hρ

/-! ### Bag-size bound -/

/-- **Lemma 2b.1 (bag-size bound)**: under rail-wise injectivity on the anchor
    and each rail, every frontier bag has at most `1 + n₂ + n₅ + n₁₁` atoms. -/
theorem frontierBag_card_le (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (hAnchor : ∀ u, Set.InjOn ρ (bagAnchor ρ u))
    (hRail2 : ∀ u, Set.InjOn (fun a => (ρ a).1) (bagRail2 ρ u))
    (hRail5 : ∀ u, Set.InjOn (fun a => (ρ a).2.1) (bagRail5 ρ u))
    (hRail11 : ∀ u, Set.InjOn (fun a => (ρ a).2.2) (bagRail11 ρ u))
    (u) :
    (frontierBag ρ u).card ≤ 1 + n₂ + n₅ + n₁₁ := by
  unfold frontierBag
  have hc := Finset.card_union_le (bagAnchor ρ u ∪ bagRail2 ρ u ∪ bagRail5 ρ u) (bagRail11 ρ u)
  have hb := Finset.card_union_le (bagAnchor ρ u ∪ bagRail2 ρ u) (bagRail5 ρ u)
  have ha := Finset.card_union_le (bagAnchor ρ u) (bagRail2 ρ u)
  have h1 := bagAnchor_card_le_one ρ u (hAnchor u)
  have h2 := bagRail2_card_le ρ u (hRail2 u)
  have h3 := bagRail5_card_le ρ u (hRail5 u)
  have h4 := bagRail11_card_le ρ u (hRail11 u)
  omega

/-- **Concrete bound** for the `n = 220` ray (caps 7, 3, 2):
    every frontier bag has at most 16 atoms. -/
theorem frontierBag_card_le_16 (ρ : β → Fin 8 × Fin 4 × Fin 3)
    (hAnchor : ∀ u, Set.InjOn ρ (bagAnchor ρ u))
    (hRail2 : ∀ u, Set.InjOn (fun a => (ρ a).1) (bagRail2 ρ u))
    (hRail5 : ∀ u, Set.InjOn (fun a => (ρ a).2.1) (bagRail5 ρ u))
    (hRail11 : ∀ u, Set.InjOn (fun a => (ρ a).2.2) (bagRail11 ρ u))
    (u) :
    (frontierBag ρ u).card ≤ 16 :=
  (frontierBag_card_le ρ hAnchor hRail2 hRail5 hRail11 u).trans (by norm_num)

/-- The canonical 16-point coordinate chart used by the bag-local witness
    certificates. -/
def frontierCoords16 : Finset (Fin 8 × Fin 4 × Fin 3) :=
  {⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨0, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩⟩,
   ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩⟩,
   ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩,
   ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩⟩,
   ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩⟩,
   ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩⟩}

theorem frontierCoords16_card : frontierCoords16.card = 16 := by
  decide

/-- Bag-local witness format for the corrected B3 proof: a single bag with an
    explicit injective coordinate assignment into the 16-point frontier chart. -/
structure FrontierBagWitness (β : Type*) [DecidableEq β] where
  bag : Finset β
  coord : β → Fin 8 × Fin 4 × Fin 3
  hInj : Set.InjOn coord bag
  hRange : ∀ a ∈ bag, coord a ∈ frontierCoords16

/-- A bag-local witness really does certify the `16`-atom frontier bound.
    This is the report-consumable B3 shape: each bag gets its own coordinate
    chart, and the seven-cell report supplies the coordinate map bag by bag. -/
theorem frontierWitness_card_le_16 {β : Type*} [DecidableEq β]
    (w : FrontierBagWitness β) : w.bag.card ≤ 16 := by
  have himg : Finset.image w.coord w.bag ⊆ frontierCoords16 := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨a, ha, rfl⟩
    exact w.hRange a ha
  have hle : (Finset.image w.coord w.bag).card ≤ frontierCoords16.card :=
    Finset.card_le_card himg
  rw [Finset.card_image_of_injOn w.hInj, frontierCoords16_card] at hle
  exact hle

/-- Bag-local B3 certificate: any explicit frontier-bag witness from the
    seven-cell report directly yields the `16`-atom bound. -/
theorem ingredient2b_bag_local {β : Type*} [DecidableEq β]
    (w : FrontierBagWitness β) : w.bag.card ≤ 16 :=
  frontierWitness_card_le_16 w

/-- Any bag with at most `16` atoms admits a canonical frontier witness into
    the `16`-point chart.  This is the constructive form that the seven-cell
    report can feed directly into Lean. -/
theorem frontierWitness_of_card_le_16 {β : Type*} [DecidableEq β]
    (bag : Finset β) (hbag : bag.card ≤ 16) :
    ∃ w : FrontierBagWitness β, w.bag = bag := by
  classical
  let eBag : ↥bag ≃ Fin bag.card := bag.equivFin
  let eFront : ↥frontierCoords16 ≃ Fin 16 := frontierCoords16.equivFin
  let chart : Fin 16 → Fin 8 × Fin 4 × Fin 3 := fun i => (eFront.symm i).1
  have hchart : Function.Injective chart := by
    intro i j hij
    apply eFront.symm.injective
    exact Subtype.ext hij
  let coord : β → Fin 8 × Fin 4 × Fin 3 := fun a =>
    if ha : a ∈ bag then chart (Fin.castLE hbag (eBag ⟨a, ha⟩))
    else chart 0
  refine ⟨{ bag := bag, coord := coord, hInj := ?_, hRange := ?_ }, rfl⟩
  · intro a ha b hb heq
    have hleft : coord a = chart (Fin.castLE hbag (eBag ⟨a, ha⟩)) := by
      dsimp [coord]
      split_ifs with h
      · rfl
      · exact (h ha).elim
    have hright : coord b = chart (Fin.castLE hbag (eBag ⟨b, hb⟩)) := by
      dsimp [coord]
      split_ifs with h
      · rfl
      · exact (h hb).elim
    rw [hleft, hright] at heq
    have h' : Fin.castLE hbag (eBag ⟨a, ha⟩) = Fin.castLE hbag (eBag ⟨b, hb⟩) :=
      hchart heq
    exact congrArg Subtype.val (eBag.injective (Fin.castLE_injective hbag h'))
  · intro a ha
    dsimp [coord]
    simp [ha]
    simp [chart, (eFront.symm (Fin.castLE hbag (eBag ⟨a, ha⟩))).2]

/-- **Ingredient 2b**: the frontier bag decomposition has the partition property
    and a bag-size bound of `1 + n₂ + n₅ + n₁₁`, assuming rail-wise injectivity
    on each local frontier fiber. -/
theorem ingredient2b (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (hAnchor : ∀ u, Set.InjOn ρ (bagAnchor ρ u))
    (hRail2 : ∀ u, Set.InjOn (fun a => (ρ a).1) (bagRail2 ρ u))
    (hRail5 : ∀ u, Set.InjOn (fun a => (ρ a).2.1) (bagRail5 ρ u))
    (hRail11 : ∀ u, Set.InjOn (fun a => (ρ a).2.2) (bagRail11 ρ u)) :
    (∀ u, Disjoint (bagAnchor ρ u) (bagRail2 ρ u)) ∧
    (∀ u, Disjoint (bagAnchor ρ u) (bagRail5 ρ u)) ∧
    (∀ u, Disjoint (bagAnchor ρ u) (bagRail11 ρ u)) ∧
    (∀ u, Disjoint (bagRail2 ρ u) (bagRail5 ρ u)) ∧
    (∀ u, Disjoint (bagRail2 ρ u) (bagRail11 ρ u)) ∧
    (∀ u, Disjoint (bagRail5 ρ u) (bagRail11 ρ u)) ∧
    (∀ u, (frontierBag ρ u).card ≤ 1 + n₂ + n₅ + n₁₁) :=
  ⟨bagAnchor_disjoint_rail2 ρ, bagAnchor_disjoint_rail5 ρ, bagAnchor_disjoint_rail11 ρ,
   bagRail2_disjoint_rail5 ρ, bagRail2_disjoint_rail11 ρ, bagRail5_disjoint_rail11 ρ,
   frontierBag_card_le ρ hAnchor hRail2 hRail5 hRail11⟩

/-- Convenience corollary: a globally injective `ρ` gives the local rail-wise
    hypotheses required by `ingredient2b`. -/
theorem ingredient2b_of_injective (ρ : β → Fin n₂ × Fin n₅ × Fin n₁₁)
    (hρ : Function.Injective ρ) :
    (∀ u, Disjoint (bagAnchor ρ u) (bagRail2 ρ u)) ∧
    (∀ u, Disjoint (bagAnchor ρ u) (bagRail5 ρ u)) ∧
    (∀ u, Disjoint (bagAnchor ρ u) (bagRail11 ρ u)) ∧
    (∀ u, Disjoint (bagRail2 ρ u) (bagRail5 ρ u)) ∧
    (∀ u, Disjoint (bagRail2 ρ u) (bagRail11 ρ u)) ∧
    (∀ u, Disjoint (bagRail5 ρ u) (bagRail11 ρ u)) ∧
    (∀ u, (frontierBag ρ u).card ≤ 1 + n₂ + n₅ + n₁₁) := by
  have hAnchor : ∀ u, Set.InjOn ρ (bagAnchor ρ u) := fun u a ha b hb heq => hρ heq
  have hRail2 : ∀ u, Set.InjOn (fun a => (ρ a).1) (bagRail2 ρ u) := by
    intro u a ha b hb heq
    have ha' : u.1 < (ρ a).1 ∧ (ρ a).2 = u.2 := by simpa [bagRail2] using ha
    have hb' : u.1 < (ρ b).1 ∧ (ρ b).2 = u.2 := by simpa [bagRail2] using hb
    exact hρ (Prod.ext heq (ha'.2.trans hb'.2.symm))
  have hRail5 : ∀ u, Set.InjOn (fun a => (ρ a).2.1) (bagRail5 ρ u) := by
    intro u a ha b hb heq
    have ha' : u.2.1 < (ρ a).2.1 ∧ (ρ a).1 = u.1 ∧ (ρ a).2.2 = u.2.2 := by
      simpa [bagRail5] using ha
    have hb' : u.2.1 < (ρ b).2.1 ∧ (ρ b).1 = u.1 ∧ (ρ b).2.2 = u.2.2 := by
      simpa [bagRail5] using hb
    have ha1 : (ρ a).1 = u.1 := ha'.2.1
    have ha22 : (ρ a).2.2 = u.2.2 := ha'.2.2
    have hb1 : (ρ b).1 = u.1 := hb'.2.1
    have hb22 : (ρ b).2.2 = u.2.2 := hb'.2.2
    exact hρ (Prod.ext (ha1.trans hb1.symm) (Prod.ext heq (ha22.trans hb22.symm)))
  have hRail11 : ∀ u, Set.InjOn (fun a => (ρ a).2.2) (bagRail11 ρ u) := by
    intro u a ha b hb heq
    have ha' : u.2.2 < (ρ a).2.2 ∧ (ρ a).1 = u.1 ∧ (ρ a).2.1 = u.2.1 := by
      simpa [bagRail11] using ha
    have hb' : u.2.2 < (ρ b).2.2 ∧ (ρ b).1 = u.1 ∧ (ρ b).2.1 = u.2.1 := by
      simpa [bagRail11] using hb
    have ha1 : (ρ a).1 = u.1 := ha'.2.1
    have ha21 : (ρ a).2.1 = u.2.1 := ha'.2.2
    have hb1 : (ρ b).1 = u.1 := hb'.2.1
    have hb21 : (ρ b).2.1 = u.2.1 := hb'.2.2
    exact hρ (Prod.ext (ha1.trans hb1.symm) (Prod.ext (ha21.trans hb21.symm) heq))
  exact ingredient2b ρ hAnchor hRail2 hRail5 hRail11

end ThreeRailDecomposition

/-! ## Ingredient 3 (lite): Separator Congruence and Interface Completeness

We abstract away the tree structure and prove the key algebraic fact underlying
the finite-state DP: the coverage mask on a shared bag `B` is a *sufficient
interface summary*.  Two fragment selections that agree on `B` are
interchangeable for any extension above `B`.

This is **Lemma 3.1** from the spec, in its tree-free algebraic form. -/

section InterfaceCompleteness

variable {α : Type*} [DecidableEq α]

/-- The coverage mask of selection `S` on bag `B`:
    atoms in `B` covered by at least one fragment in `S`. -/
def coverMask (S : Finset (Finset α)) (B : Finset α) : Finset α :=
  S.biUnion id ∩ B

/-- Two selections are **interface-equivalent** at `B` when they cover the
    same subset of `B`. -/
def InterfaceEquiv (B : Finset α) (S S' : Finset (Finset α)) : Prop :=
  coverMask S B = coverMask S' B

theorem interfaceEquiv_refl (B : Finset α) (S : Finset (Finset α)) :
    InterfaceEquiv B S S := rfl

theorem interfaceEquiv_symm {B : Finset α} {S S' : Finset (Finset α)}
    (h : InterfaceEquiv B S S') : InterfaceEquiv B S' S := h.symm

theorem interfaceEquiv_trans {B : Finset α} {S S' S'' : Finset (Finset α)}
    (h : InterfaceEquiv B S S') (k : InterfaceEquiv B S' S'') :
    InterfaceEquiv B S S'' := h.trans k

/-- `biUnion` distributes over `∪` in the index family.  Helper for
    `interfaceMask_congruence`. -/
private lemma biUnion_union_index (S E : Finset (Finset α)) :
    (S ∪ E).biUnion id = S.biUnion id ∪ E.biUnion id := by
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_union, id]
  constructor
  · rintro ⟨t, ht | ht, ha⟩
    · exact Or.inl ⟨t, ht, ha⟩
    · exact Or.inr ⟨t, ht, ha⟩
  · rintro (⟨t, ht, ha⟩ | ⟨t, ht, ha⟩)
    · exact ⟨t, Or.inl ht, ha⟩
    · exact ⟨t, Or.inr ht, ha⟩

/-- **Lemma 3.1 (Interface Completeness)**: interface equivalence is a
    congruence for extension — adding the same set `E` of fragments above
    `B` preserves the equivalence class. -/
theorem interfaceMask_congruence (B : Finset α) {S S' E : Finset (Finset α)}
    (h : InterfaceEquiv B S S') : InterfaceEquiv B (S ∪ E) (S' ∪ E) := by
  unfold InterfaceEquiv coverMask
  rw [biUnion_union_index, biUnion_union_index,
      Finset.union_inter_distrib_right, Finset.union_inter_distrib_right,
      show S.biUnion id ∩ B = S'.biUnion id ∩ B from h]

/-- The number of distinct interface masks at bag `B` is exactly `2^|B|`,
    bounding the DP state space per node. -/
theorem interface_state_count [Fintype α] (B : Finset α) :
    Fintype.card (Finset ↑B) = 2 ^ B.card := by
  rw [Fintype.card_finset, Fintype.card_coe]

/-- **Ingredient 3 (lite)**: the separator-congruence property and finite-state
    bound.  Together they justify the finite-state DP: any two subtree selections
    with identical bag masks are interchangeable above the bag, and the state
    space per node has at most `2^|B(u)|` entries. -/
theorem ingredient3_lite [Fintype α] (B : Finset α) :
    (∀ S S' E : Finset (Finset α),
      InterfaceEquiv B S S' → InterfaceEquiv B (S ∪ E) (S' ∪ E)) ∧
    Fintype.card (Finset ↑B) = 2 ^ B.card :=
  ⟨fun _ _ _ h => interfaceMask_congruence B h, interface_state_count B⟩

end InterfaceCompleteness

/-! ## Ingredient 3: DP Recurrence Correctness (tree-free core)

The full DP[u,s]=OPT[u,s] proof (Lemma 3.2) needs a rooted tree-decomposition
type for its induction, which the pinned Mathlib release does not supply.  This
section first
proves the two combinatorial lemmas that *are* the inductive step; the rooted
tree itself (`NTD`) and the full induction (`ingredient3_full`) are built further
down in this file, so the tree-free framing here is the order of presentation,
not a limitation of what is proved:

* **`feasible_union`** (completeness): combining two disjoint-interior feasible
  selections yields a feasible selection for the combined problem.
* **`feasible_decompose`** (soundness): every feasible selection decomposes by a
  fragment-family partition with additive cost and split mask.

Together with Lemma 3.1 (separator congruence, already proved), these two lemmas
constitute the mathematical core of Lemma 3.2.  The full induction follows by
applying them bottom-up on any concrete rooted tree of bags. -/

section RecurrenceCorrectness

variable {α : Type*} [DecidableEq α]

/-- `S` is **feasible** for `(B, I, s)`: it covers all interior atoms `I` and
    induces exactly the coverage mask `s` on bag `B`. -/
def Feasible (B I s : Finset α) (S : Finset (Finset α)) : Prop :=
  I ⊆ S.biUnion id ∧ coverMask S B = s

private lemma biUnion_id_union (L R : Finset (Finset α)) :
    (L ∪ R).biUnion id = L.biUnion id ∪ R.biUnion id := by
  ext a; simp only [Finset.mem_biUnion, Finset.mem_union, id]
  constructor
  · rintro ⟨t, ht | ht, ha⟩; exact Or.inl ⟨t, ht, ha⟩; exact Or.inr ⟨t, ht, ha⟩
  · rintro (⟨t, ht, ha⟩ | ⟨t, ht, ha⟩); exact ⟨t, Or.inl ht, ha⟩; exact ⟨t, Or.inr ht, ha⟩

private lemma coverMask_union_eq (L R : Finset (Finset α)) (B : Finset α) :
    coverMask (L ∪ R) B = coverMask L B ∪ coverMask R B := by
  simp only [coverMask, biUnion_id_union, Finset.union_inter_distrib_right]

/-- **Completeness** (Lemma 3.2 completeness direction): merging two feasible
    selections whose interiors are disjoint yields a feasible selection for the
    combined interior and the union of the two masks. -/
theorem feasible_union {B I_L I_R s_L s_R : Finset α}
    {L R : Finset (Finset α)}
    (hL : Feasible B I_L s_L L) (hR : Feasible B I_R s_R R) :
    Feasible B (I_L ∪ I_R) (s_L ∪ s_R) (L ∪ R) := by
  refine ⟨fun a ha => ?_, ?_⟩
  · simp only [Finset.mem_union] at ha
    simp only [biUnion_id_union, Finset.mem_union]
    rcases ha with haL | haR
    · exact Or.inl (hL.1 haL)
    · exact Or.inr (hR.1 haR)
  · rw [coverMask_union_eq, hL.2, hR.2]

/-- **Soundness** (Lemma 3.2 soundness direction): every feasible selection
    decomposes by any fragment-family partition into two disjoint parts, with
    additive cardinality and split coverage mask. -/
theorem feasible_decompose {B I s : Finset α} {S : Finset (Finset α)}
    (hS : Feasible B I s S) (Loc : Finset (Finset α)) :
    let L := S.filter (· ∈ Loc)
    let R := S.filter (· ∉ Loc)
    Disjoint L R ∧
    S.card = L.card + R.card ∧
    coverMask S B = coverMask L B ∪ coverMask R B := by
  have hSplit : S.filter (· ∈ Loc) ∪ S.filter (· ∉ Loc) = S := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter]
    exact ⟨fun h => h.elim (·.1) (·.1),
           fun h => (em (a ∈ Loc)).elim (Or.inl ⟨h, ·⟩) (Or.inr ⟨h, ·⟩)⟩
  have hDisj : Disjoint (S.filter (· ∈ Loc)) (S.filter (· ∉ Loc)) :=
    Finset.disjoint_filter.mpr (fun _ _ h hne => hne h)
  refine ⟨hDisj, ?_, ?_⟩
  · rw [← Finset.card_union_of_disjoint hDisj, hSplit]
  · conv_lhs => rw [show S = S.filter (· ∈ Loc) ∪ S.filter (· ∉ Loc) from hSplit.symm]
    exact coverMask_union_eq _ _ _

/-- **Ingredient 3 (core)**: bundles the completeness and soundness lemmas.
    These two results are the tree-free inductive core of Lemma 3.2
    (DP[u,s] = OPT[u,s]).  Given correct child tables, one application of
    `feasible_union` (combining child solutions) proves OPT ≤ DP, and one
    application of `feasible_decompose` (partitioning the optimal solution)
    proves DP ≤ OPT. -/
theorem ingredient3 (B : Finset α) :
    (∀ {I_L I_R s_L s_R : Finset α} {L R : Finset (Finset α)},
      Feasible B I_L s_L L → Feasible B I_R s_R R →
      Feasible B (I_L ∪ I_R) (s_L ∪ s_R) (L ∪ R)) ∧
    (∀ {I s : Finset α} {S : Finset (Finset α)} (Loc : Finset (Finset α)),
      Feasible B I s S →
      Disjoint (S.filter (· ∈ Loc)) (S.filter (· ∉ Loc)) ∧
      S.card = (S.filter (· ∈ Loc)).card + (S.filter (· ∉ Loc)).card ∧
      coverMask S B = coverMask (S.filter (· ∈ Loc)) B ∪
                      coverMask (S.filter (· ∉ Loc)) B) :=
  ⟨fun hL hR => feasible_union hL hR,
   fun Loc hS => feasible_decompose hS Loc⟩

end RecurrenceCorrectness

/-! ## Lemma 3.2 Full Induction: Nice Tree Decomposition

This section provides the rooted-tree infrastructure for the full
`DP[u,s] = OPT[u,s]` induction of Lemma 3.2 (Ingredient 3).  The four
nice-decomp node kinds are encoded in `NTD`.  The main results
`NTD.join_assemble` (completeness) and `NTD.join_decompose` (soundness)
prove that optimal selections factor through join nodes; together with
`NTD.leaf_feasible` they close the structural induction on any WF NTD. -/

section TreeInduction

/-- A nice tree decomposition over atom type `β`.  Each node carries `lf`,
    the set of fragments locally introduced at that node (highest bag = this bag).
    Instantiate `β := α` for the running atom type. -/
inductive NTD.{u} (β : Type u) : Type u where
  | leaf : NTD β
  | introduce (a : β) (lf : Finset (Finset β)) (child : NTD β) : NTD β
  | forget    (a : β) (lf : Finset (Finset β)) (child : NTD β) : NTD β
  | join      (lf : Finset (Finset β)) (left right : NTD β)    : NTD β

/-- Bag of atoms at this node. -/
def NTD.bag {β : Type*} [DecidableEq β] : NTD β → Finset β
  | .leaf           => ∅
  | .introduce a _ t => insert a t.bag
  | .forget    a _ t => t.bag.erase a
  | .join      _ l _ => l.bag

/-- Atoms forgotten inside the subtree that must be covered before leaving. -/
def NTD.interior {β : Type*} [DecidableEq β] : NTD β → Finset β
  | .leaf           => ∅
  | .introduce _ _ t => t.interior
  | .forget    a _ t => insert a t.interior
  | .join      _ l r => l.interior ∪ r.interior

/-- All fragment sets introduced anywhere in the subtree. -/
def NTD.allFrags {β : Type*} [DecidableEq β] : NTD β → Finset (Finset β)
  | .leaf           => ∅
  | .introduce _ lf t => lf ∪ t.allFrags
  | .forget    _ lf t => lf ∪ t.allFrags
  | .join      lf l r => lf ∪ l.allFrags ∪ r.allFrags

/-- Maximum bag cardinality over every node in a nice tree decomposition. -/
def NTD.maxBagCard {β : Type*} [DecidableEq β] : NTD β → ℕ
  | .leaf => 0
  | .introduce a _ t => max (insert a t.bag).card t.maxBagCard
  | .forget a _ t => max (t.bag.erase a).card t.maxBagCard
  | .join _ l r => max l.bag.card (max l.maxBagCard r.maxBagCard)

/-- Well-formedness of a nice tree decomposition.  The join conditions encode:
    bags agree between children, fragment families are pairwise disjoint,
    local fragments fit in the current bag, and each subtree's fragments
    cannot reach the other subtree's interior (tree-decomposition separator property). -/
inductive NTD.WF {β : Type*} [DecidableEq β] : NTD β → Prop where
  | leaf : NTD.WF (.leaf (β := β))
  | introduce {a lf t} (ha_bag : a ∉ t.bag) (ha_int : a ∉ t.interior)
      (hlf_sub : ∀ F ∈ lf, F ⊆ insert a t.bag)
      (ht : NTD.WF t) : NTD.WF (.introduce a lf t)
  | forget {a lf t} (ha : a ∈ t.bag)
      (hlf_sub : ∀ F ∈ lf, F ⊆ t.bag.erase a)
      (ht : NTD.WF t) : NTD.WF (.forget a lf t)
  | join {lf l r}
      (hbag     : l.bag = r.bag)
      (hd       : Disjoint l.allFrags r.allFrags)
      (hlf_sub  : ∀ F ∈ lf, F ⊆ l.bag)
      (hlf_disj : Disjoint lf (l.allFrags ∪ r.allFrags))
      (hsep_l   : ∀ F ∈ r.allFrags, ∀ a ∈ l.interior, a ∉ F)
      (hsep_r   : ∀ F ∈ l.allFrags, ∀ a ∈ r.interior, a ∉ F)
      (hl : NTD.WF l) (hr : NTD.WF r) : NTD.WF (.join lf l r)

/-- Executable checker for all side conditions in `NTD.WF`. -/
def NTD.wfCheck {β : Type*} [DecidableEq β] : NTD β → Bool
  | .leaf => true
  | .introduce a lf t =>
      decide (a ∉ t.bag) &&
      decide (a ∉ t.interior) &&
      decide (∀ F ∈ lf, F ⊆ insert a t.bag) &&
      t.wfCheck
  | .forget a lf t =>
      decide (a ∈ t.bag) &&
      decide (∀ F ∈ lf, F ⊆ t.bag.erase a) &&
      t.wfCheck
  | .join lf l r =>
      decide (l.bag = r.bag) &&
      decide (Disjoint l.allFrags r.allFrags) &&
      decide (∀ F ∈ lf, F ⊆ l.bag) &&
      decide (Disjoint lf (l.allFrags ∪ r.allFrags)) &&
      decide (∀ F ∈ r.allFrags, ∀ a ∈ l.interior, a ∉ F) &&
      decide (∀ F ∈ l.allFrags, ∀ a ∈ r.interior, a ∉ F) &&
      l.wfCheck && r.wfCheck

/-- The executable checker is equivalent to propositional well-formedness. -/
theorem NTD.wfCheck_eq_true_iff {β : Type*} [DecidableEq β] {t : NTD β} :
    t.wfCheck = true ↔ t.WF := by
  induction t with
  | leaf =>
      constructor
      · intro
        exact .leaf
      · intro
        rfl
  | introduce a lf t ih =>
      simp only [NTD.wfCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · intro h
        rcases h with ⟨⟨⟨ha_bag, ha_int⟩, hlf_sub⟩, ht⟩
        exact .introduce ha_bag ha_int hlf_sub ht
      · intro ht
        cases ht with
        | introduce ha_bag ha_int hlf_sub ht =>
            exact ⟨⟨⟨ha_bag, ha_int⟩, hlf_sub⟩, ht⟩
  | forget a lf t ih =>
      simp only [NTD.wfCheck, Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · rintro ⟨⟨ha, hlf_sub⟩, ht⟩
        exact .forget ha hlf_sub ht
      · intro ht
        cases ht with
        | forget ha hlf_sub ht =>
            exact ⟨⟨ha, hlf_sub⟩, ht⟩
  | join lf l r ihl ihr =>
      simp only [NTD.wfCheck, Bool.and_eq_true, decide_eq_true_eq, ihl, ihr]
      constructor
      · rintro ⟨⟨⟨⟨⟨⟨⟨hbag, hd⟩, hlf_sub⟩, hlf_disj⟩, hsep_l⟩, hsep_r⟩, hl⟩, hr⟩
        exact .join hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr
      · intro ht
        cases ht with
        | join hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr =>
            exact
              ⟨⟨⟨⟨⟨⟨⟨hbag, hd⟩, hlf_sub⟩, hlf_disj⟩, hsep_l⟩, hsep_r⟩, hl⟩, hr⟩

/-- In any WF NTD, interior atoms and bag atoms are always disjoint. -/
theorem NTD.WF.interior_bag_disj {β : Type*} [DecidableEq β] {t : NTD β}
    (ht : NTD.WF t) : Disjoint t.interior t.bag := by
  induction ht with
  | leaf => simp [NTD.interior, NTD.bag]
  | introduce ha_bag ha_int _ _ ih =>
      simp only [NTD.interior, NTD.bag, Finset.disjoint_insert_right]
      exact ⟨ha_int, ih⟩
  | forget _ _ _ ih =>
      simp only [NTD.interior, NTD.bag, Finset.disjoint_insert_left]
      refine ⟨?_, ih.mono_right (Finset.erase_subset _ _)⟩
      simp [Finset.mem_erase]
  | join hbag _ _ _ _ _ _ _ ihl ihr =>
      simp only [NTD.interior, NTD.bag, Finset.disjoint_union_left]
      exact ⟨ihl, hbag.symm ▸ ihr⟩

/-- A selection `S` is **subtree-feasible** for node `t` with mask `s`:
    it draws fragments only from `t.allFrags`, covers `t.interior`,
    and achieves coverage mask `s` on `t.bag`. -/
def SubFeasible (t : NTD α) (s : Finset α) (S : Finset (Finset α)) : Prop :=
  S ⊆ t.allFrags ∧ Feasible t.bag t.interior s S

/-- **Leaf base case**: the only subtree-feasible selection for a leaf is empty. -/
theorem NTD.leaf_feasible {s : Finset α} {S : Finset (Finset α)} :
    SubFeasible (.leaf : NTD α) s S ↔ S = ∅ ∧ s = ∅ := by
  simp only [SubFeasible, NTD.allFrags, Feasible, NTD.interior, NTD.bag, coverMask,
             Finset.subset_empty, Finset.empty_subset, Finset.inter_empty, true_and, eq_comm]

/-- **Introduce assembly** (Lemma 3.2 completeness at introduce nodes): a child
    selection and a local fragment selection combine into a feasible introduce-node
    selection.  The mask on the enlarged bag is determined by the union `Sl ∪ Sc`. -/
theorem NTD.introduce_assemble {a : α} {lf : Finset (Finset α)} {t : NTD α}
    {Sl Sc : Finset (Finset α)} {sc : Finset α}
    (hSl : Sl ⊆ lf) (hSc : SubFeasible t sc Sc) :
    SubFeasible (.introduce a lf t) (coverMask (Sl ∪ Sc) (insert a t.bag)) (Sl ∪ Sc) := by
  obtain ⟨hSc_sub, hSc_feas⟩ := hSc
  obtain ⟨hSc_cov, -⟩ := hSc_feas
  refine ⟨?_, ?_, rfl⟩
  · simp only [NTD.allFrags]
    exact Finset.union_subset (hSl.trans Finset.subset_union_left)
                              (hSc_sub.trans Finset.subset_union_right)
  · simp only [NTD.interior]
    exact hSc_cov.trans (fun x hx =>
      let ⟨F, hFS, hxF⟩ := Finset.mem_biUnion.mp hx
      Finset.mem_biUnion.mpr ⟨F, Finset.mem_union_right _ hFS, hxF⟩)

/-- **Introduce decomposition** (Lemma 3.2 soundness at introduce nodes): any
    subtree-feasible selection restricts to a child-feasible selection.  The WF
    condition `hlf_sub` ensures local fragments fit within the current bag and
    therefore cannot cover child-interior atoms. -/
theorem NTD.introduce_decompose {a : α} {lf : Finset (Finset α)} {t : NTD α}
    {s : Finset α} {S : Finset (Finset α)}
    (hWF : NTD.WF (.introduce a lf t)) (hS : SubFeasible (.introduce a lf t) s S) :
    SubFeasible t (coverMask (S.filter (· ∈ t.allFrags)) t.bag)
                  (S.filter (· ∈ t.allFrags)) := by
  obtain ⟨hS_sub, hS_feas⟩ := hS
  simp only [NTD.allFrags] at hS_sub
  simp only [NTD.bag, NTD.interior] at hS_feas
  obtain ⟨hS_cov, -⟩ := hS_feas
  cases hWF with
  | introduce ha_bag ha_int hlf_sub ht =>
  have loc : ∀ a' ∈ t.interior, ∀ F ∈ S, a' ∈ F → F ∈ t.allFrags := by
    intro a' ha' F hFS haF
    rcases Finset.mem_union.mp (hS_sub hFS) with hFl | hFt
    · have hFsub := hlf_sub F hFl
      have ha'_in : a' ∈ insert a t.bag := hFsub haF
      simp only [Finset.mem_insert] at ha'_in
      rcases ha'_in with rfl | ha'_bag
      · exact absurd ha' ha_int
      · exact absurd ha'_bag (Finset.disjoint_left.mp ht.interior_bag_disj ha')
    · exact hFt
  refine ⟨fun F hF => (Finset.mem_filter.mp hF).2, fun a' ha' => ?_, rfl⟩
  obtain ⟨F, hFS, haF⟩ := Finset.mem_biUnion.mp (hS_cov ha')
  exact Finset.mem_biUnion.mpr ⟨F, Finset.mem_filter.mpr ⟨hFS, loc a' ha' F hFS haF⟩, haF⟩

/-- **Forget assembly** (Lemma 3.2 completeness at forget nodes): a child selection
    and a local fragment selection combine into a feasible forget-node selection,
    provided atom `a` (which moves from bag to interior) is already covered. -/
theorem NTD.forget_assemble {a : α} {lf : Finset (Finset α)} {t : NTD α}
    {Sl Sc : Finset (Finset α)} {sc : Finset α}
    (hSl : Sl ⊆ lf) (hSc : SubFeasible t sc Sc)
    (ha_cov : a ∈ (Sl ∪ Sc).biUnion id) :
    SubFeasible (.forget a lf t) (coverMask (Sl ∪ Sc) (t.bag.erase a)) (Sl ∪ Sc) := by
  obtain ⟨hSc_sub, hSc_feas⟩ := hSc
  obtain ⟨hSc_cov, -⟩ := hSc_feas
  refine ⟨?_, ?_, rfl⟩
  · simp only [NTD.allFrags]
    exact Finset.union_subset (hSl.trans Finset.subset_union_left)
                              (hSc_sub.trans Finset.subset_union_right)
  · simp only [NTD.interior, Finset.insert_subset_iff]
    exact ⟨ha_cov, hSc_cov.trans (fun x hx =>
      let ⟨F, hFS, hxF⟩ := Finset.mem_biUnion.mp hx
      Finset.mem_biUnion.mpr ⟨F, Finset.mem_union_right _ hFS, hxF⟩)⟩

/-- **Forget decomposition** (Lemma 3.2 soundness at forget nodes): any
    subtree-feasible selection at a forget node restricts to a child-feasible
    selection.  The WF condition `hlf_sub` ensures local fragments fit within
    the forget-node bag and cannot cover child-interior atoms. -/
theorem NTD.forget_decompose {a : α} {lf : Finset (Finset α)} {t : NTD α}
    {s : Finset α} {S : Finset (Finset α)}
    (hWF : NTD.WF (.forget a lf t)) (hS : SubFeasible (.forget a lf t) s S) :
    SubFeasible t (coverMask (S.filter (· ∈ t.allFrags)) t.bag)
                  (S.filter (· ∈ t.allFrags)) := by
  obtain ⟨hS_sub, hS_feas⟩ := hS
  simp only [NTD.allFrags] at hS_sub
  simp only [NTD.bag, NTD.interior] at hS_feas
  obtain ⟨hS_cov, -⟩ := hS_feas
  cases hWF with
  | forget ha hlf_sub ht =>
  have loc : ∀ a' ∈ t.interior, ∀ F ∈ S, a' ∈ F → F ∈ t.allFrags := by
    intro a' ha' F hFS haF
    rcases Finset.mem_union.mp (hS_sub hFS) with hFl | hFt
    · have hFsub := hlf_sub F hFl
      have ha'_in : a' ∈ t.bag.erase a := hFsub haF
      rw [Finset.mem_erase] at ha'_in
      exact absurd ha'_in.2 (Finset.disjoint_left.mp ht.interior_bag_disj ha')
    · exact hFt
  refine ⟨fun F hF => (Finset.mem_filter.mp hF).2, fun a' ha' => ?_, rfl⟩
  obtain ⟨F, hFS, haF⟩ := Finset.mem_biUnion.mp (hS_cov (Finset.mem_insert_of_mem ha'))
  exact Finset.mem_biUnion.mpr ⟨F, Finset.mem_filter.mpr ⟨hFS, loc a' ha' F hFS haF⟩, haF⟩

/-- **Join assembly** (Lemma 3.2 completeness at join nodes): feasible child
    selections combine into a feasible parent selection. -/
theorem NTD.join_assemble {lf : Finset (Finset α)} {l r : NTD α}
    {sl sr : Finset α} {Sl Sr : Finset (Finset α)}
    (hWF : NTD.WF (.join lf l r))
    (hSl : SubFeasible l sl Sl) (hSr : SubFeasible r sr Sr) :
    SubFeasible (.join lf l r) (sl ∪ sr) (Sl ∪ Sr) := by
  obtain ⟨hSl_sub, hSl_feas⟩ := hSl
  obtain ⟨hSr_sub, hSr_feas⟩ := hSr
  cases hWF with
  | join hbag _ _ _ _ _ _ _ =>
  refine ⟨?_, ?_⟩
  · simp only [NTD.allFrags]
    exact Finset.union_subset
      (hSl_sub.trans (Finset.subset_union_right.trans Finset.subset_union_left))
      (hSr_sub.trans Finset.subset_union_right)
  · simp only [NTD.bag, NTD.interior]
    rw [← hbag] at hSr_feas
    exact feasible_union hSl_feas hSr_feas

/-- **Join decomposition** (Lemma 3.2 soundness at join nodes): any subtree-feasible
    selection decomposes into feasible parts for the two children.
    The separator conditions in `WF` ensure that each subtree's fragments
    can only cover their own interior. -/
theorem NTD.join_decompose {lf : Finset (Finset α)} {l r : NTD α}
    {s : Finset α} {S : Finset (Finset α)}
    (hWF : NTD.WF (.join lf l r)) (hS : SubFeasible (.join lf l r) s S) :
    SubFeasible l (coverMask (S.filter (· ∈ l.allFrags)) l.bag)
                  (S.filter (· ∈ l.allFrags)) ∧
    SubFeasible r (coverMask (S.filter (· ∈ r.allFrags)) r.bag)
                  (S.filter (· ∈ r.allFrags)) := by
  obtain ⟨hS_sub, hFeas⟩ := hS
  simp only [NTD.bag, NTD.interior] at hFeas
  obtain ⟨hcov, -⟩ := hFeas
  cases hWF with
  | join hbag hd hlf_sub _ hsep_l hsep_r hl hr =>
  have hS_sub' : S ⊆ lf ∪ l.allFrags ∪ r.allFrags := by
    simpa only [NTD.allFrags] using hS_sub
  -- Key: any fragment in S covering an atom in l.interior must be in l.allFrags
  have left_loc : ∀ a ∈ l.interior, ∀ F ∈ S, a ∈ F → F ∈ l.allFrags := fun a ha F hFS haF => by
    rcases (by simpa only [Finset.mem_union] using hS_sub' hFS) with ((hFlf | hFl) | hFr)
    · exact absurd (hlf_sub F hFlf haF)
                   (Finset.disjoint_left.mp (hl.interior_bag_disj) ha)
    · exact hFl
    · exact absurd haF (hsep_l F hFr a ha)
  -- Key: any fragment in S covering an atom in r.interior must be in r.allFrags
  have right_loc : ∀ a ∈ r.interior, ∀ F ∈ S, a ∈ F → F ∈ r.allFrags := fun a ha F hFS haF => by
    rcases (by simpa only [Finset.mem_union] using hS_sub' hFS) with ((hFlf | hFl) | hFr)
    · have : a ∉ r.bag := Finset.disjoint_left.mp hr.interior_bag_disj ha
      exact absurd (hbag ▸ (hlf_sub F hFlf haF)) this
    · exact absurd haF (hsep_r F hFl a ha)
    · exact hFr
  constructor
  · refine ⟨fun F hF => (Finset.mem_filter.mp hF).2, fun a ha => ?_, rfl⟩
    obtain ⟨F, hFS, haF⟩ := Finset.mem_biUnion.mp (hcov (Finset.mem_union_left _ ha))
    exact Finset.mem_biUnion.mpr
      ⟨F, Finset.mem_filter.mpr ⟨hFS, left_loc a ha F hFS haF⟩, haF⟩
  · refine ⟨fun F hF => (Finset.mem_filter.mp hF).2, fun a ha => ?_, rfl⟩
    obtain ⟨F, hFS, haF⟩ := Finset.mem_biUnion.mp (hcov (Finset.mem_union_right _ ha))
    exact Finset.mem_biUnion.mpr
      ⟨F, Finset.mem_filter.mpr ⟨hFS, right_loc a ha F hFS haF⟩, haF⟩

/-- Every fragment recorded below a well-formed node is supported on that
    node's bag or interior. -/
theorem NTD.WF.allFrags_subset_bag_union_interior {t : NTD α} (ht : NTD.WF t) :
    ∀ F ∈ t.allFrags, F ⊆ t.bag ∪ t.interior := by
  induction ht with
  | leaf =>
      simp [NTD.allFrags]
  | @introduce a lf t ha_bag ha_int hlf_sub ht ih =>
      intro F hF
      simp only [NTD.allFrags, Finset.mem_union] at hF
      simp only [NTD.bag, NTD.interior]
      rcases hF with hF | hF
      · exact (hlf_sub F hF).trans Finset.subset_union_left
      · intro x hx
        rcases Finset.mem_union.mp (ih F hF hx) with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hx)
        · exact Finset.mem_union_right _ hx
  | @forget a lf t ha hlf_sub ht ih =>
      intro F hF
      simp only [NTD.allFrags, Finset.mem_union] at hF
      simp only [NTD.bag, NTD.interior]
      rcases hF with hF | hF
      · exact (hlf_sub F hF).trans Finset.subset_union_left
      · intro x hx
        rcases Finset.mem_union.mp (ih F hF hx) with hx | hx
        · by_cases hxa : x = a
          · subst x
            exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxa, hx⟩)
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hx)
  | @join lf l r hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr ihl ihr =>
      intro F hF
      simp only [NTD.allFrags, Finset.mem_union] at hF
      simp only [NTD.bag, NTD.interior]
      rcases hF with (hF | hF) | hF
      · exact (hlf_sub F hF).trans Finset.subset_union_left
      · intro x hx
        rcases Finset.mem_union.mp (ihl F hF hx) with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hx)
      · intro x hx
        rcases Finset.mem_union.mp (ihr F hF hx) with hx | hx
        · exact Finset.mem_union_left _ (hbag ▸ hx)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ hx)

/-- Locally introduced fragments that have not already appeared in the child. -/
def NTD.freshLocal (lf : Finset (Finset α)) (t : NTD α) : Finset (Finset α) :=
  lf \ t.allFrags

/-- Executable recursive table of exact feasible states and their selected
    fragment witnesses.  Each row is `(bag mask, selected fragments)`. -/
def NTD.solutionTable : NTD α → Finset (Finset α × Finset (Finset α))
  | .leaf => {(∅, ∅)}
  | .introduce a lf t =>
      ((freshLocal lf t).powerset ×ˢ t.solutionTable).image fun entry =>
        let L := entry.1
        let child := entry.2
        let S := L ∪ child.2
        (coverMask S (insert a t.bag), S)
  | .forget a lf t =>
      (((freshLocal lf t).powerset ×ˢ t.solutionTable).filter fun entry =>
        a ∈ (entry.1 ∪ entry.2.2).biUnion id).image fun entry =>
          let L := entry.1
          let child := entry.2
          let S := L ∪ child.2
          (coverMask S (t.bag.erase a), S)
  | .join lf l r =>
      (lf.powerset ×ˢ (l.solutionTable ×ˢ r.solutionTable)).image fun entry =>
        let L := entry.1
        let left := entry.2.1
        let right := entry.2.2
        let S := L ∪ left.2 ∪ right.2
        (coverMask S l.bag, S)

private theorem filter_not_mem_union_filter_mem (S Loc : Finset (Finset α)) :
    S.filter (· ∉ Loc) ∪ S.filter (· ∈ Loc) = S := by
  ext F
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hF, -⟩ | ⟨hF, -⟩)
    · exact hF
    · exact hF
  · intro hF
    exact (em (F ∈ Loc)).elim (fun h ↦ Or.inr ⟨hF, h⟩) (fun h ↦ Or.inl ⟨hF, h⟩)

private theorem SubFeasible.add_left {t : NTD α} {s : Finset α}
    {S L : Finset (Finset α)} (hS : SubFeasible t s S) (hL : L ⊆ t.allFrags) :
    SubFeasible t (coverMask (L ∪ S) t.bag) (L ∪ S) := by
  refine ⟨Finset.union_subset hL hS.1, ?_, rfl⟩
  exact hS.2.1.trans fun x hx ↦
    let ⟨F, hFS, hxF⟩ := Finset.mem_biUnion.mp hx
    Finset.mem_biUnion.mpr ⟨F, Finset.mem_union_right _ hFS, hxF⟩

/-- Every row generated by `solutionTable` is semantically subtree-feasible. -/
theorem NTD.solutionTable_sound {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} {S : Finset (Finset α)} (hmem : (s, S) ∈ t.solutionTable) :
    SubFeasible t s S := by
  induction hWF generalizing s S with
  | leaf =>
      simp only [NTD.solutionTable, Finset.mem_singleton, Prod.mk.injEq] at hmem
      exact NTD.leaf_feasible.mpr ⟨hmem.2, hmem.1⟩
  | @introduce a lf t ha_bag ha_int hlf_sub ht ih =>
      simp only [NTD.solutionTable, Finset.mem_image, Finset.mem_product,
        Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, sc, Sc⟩, ⟨hL, hchild⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hS
      subst s
      subst S
      exact NTD.introduce_assemble (hL.trans Finset.sdiff_subset) (ih hchild)
  | @forget a lf t ha hlf_sub ht ih =>
      simp only [NTD.solutionTable, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product, Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, sc, Sc⟩, ⟨⟨hL, hchild⟩, ha_cov⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hS
      subst s
      subst S
      exact NTD.forget_assemble (hL.trans Finset.sdiff_subset) (ih hchild) ha_cov
  | @join lf l r hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr ihl ihr =>
      simp only [NTD.solutionTable, Finset.mem_image, Finset.mem_product,
        Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, ⟨sl, Sl⟩, sr, Sr⟩, ⟨hL, hleft, hright⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hS
      subst s
      subst S
      have hchildren : SubFeasible (.join lf l r) (sl ∪ sr) (Sl ∪ Sr) :=
        NTD.join_assemble (.join hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr)
          (ihl hleft) (ihr hright)
      have hlocal : L ⊆ (NTD.join lf l r).allFrags := by
        intro F hF
        simp only [NTD.allFrags, Finset.mem_union]
        exact Or.inl (Or.inl (hL hF))
      -- Lean 4.31+ closes `simpa using` at reducible transparency, so unfold
      -- the recursive bag definition explicitly.
      simpa only [NTD.bag, Finset.union_assoc] using hchildren.add_left hlocal

/-- Every semantically subtree-feasible selection occurs as an exact row in
    `solutionTable`. -/
theorem NTD.solutionTable_complete {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} {S : Finset (Finset α)} (hS : SubFeasible t s S) :
    (s, S) ∈ t.solutionTable := by
  induction hWF generalizing s S with
  | leaf =>
      obtain ⟨rfl, rfl⟩ := NTD.leaf_feasible.mp hS
      simp [NTD.solutionTable]
  | @introduce a lf t ha_bag ha_int hlf_sub ht ih =>
      let Sc := S.filter (· ∈ t.allFrags)
      let L := S.filter (· ∉ t.allFrags)
      let sc := coverMask Sc t.bag
      have hchild : SubFeasible t sc Sc :=
        NTD.introduce_decompose (.introduce ha_bag ha_int hlf_sub ht) hS
      have hchildmem : (sc, Sc) ∈ t.solutionTable := ih hchild
      have hL : L ⊆ NTD.freshLocal lf t := by
        intro F hF
        have hFS := (Finset.mem_filter.mp hF).1
        have hFnot := (Finset.mem_filter.mp hF).2
        have hFall := hS.1 hFS
        simp only [NTD.allFrags, Finset.mem_union] at hFall
        exact Finset.mem_sdiff.mpr ⟨hFall.resolve_right hFnot, hFnot⟩
      have hsplit : L ∪ Sc = S := filter_not_mem_union_filter_mem S t.allFrags
      have hmask : coverMask S (insert a t.bag) = s := by
        simpa only [NTD.bag] using hS.2.2
      simp only [NTD.solutionTable, Finset.mem_image]
      refine ⟨(L, sc, Sc), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hL, hchildmem⟩
      · simp only
        rw [hsplit, hmask]
  | @forget a lf t ha hlf_sub ht ih =>
      let Sc := S.filter (· ∈ t.allFrags)
      let L := S.filter (· ∉ t.allFrags)
      let sc := coverMask Sc t.bag
      have hchild : SubFeasible t sc Sc :=
        NTD.forget_decompose (.forget ha hlf_sub ht) hS
      have hchildmem : (sc, Sc) ∈ t.solutionTable := ih hchild
      have hL : L ⊆ NTD.freshLocal lf t := by
        intro F hF
        have hFS := (Finset.mem_filter.mp hF).1
        have hFnot := (Finset.mem_filter.mp hF).2
        have hFall := hS.1 hFS
        simp only [NTD.allFrags, Finset.mem_union] at hFall
        exact Finset.mem_sdiff.mpr ⟨hFall.resolve_right hFnot, hFnot⟩
      have hsplit : L ∪ Sc = S := filter_not_mem_union_filter_mem S t.allFrags
      have ha_cov : a ∈ S.biUnion id :=
        hS.2.1 (by simp [NTD.interior])
      have hmask : coverMask S (t.bag.erase a) = s := by
        simpa only [NTD.bag] using hS.2.2
      simp only [NTD.solutionTable, Finset.mem_image]
      refine ⟨(L, sc, Sc), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hL, hchildmem⟩,
            hsplit ▸ ha_cov⟩
      · simp only
        rw [hsplit, hmask]
  | @join lf l r hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr ihl ihr =>
      let Sl := S.filter (· ∈ l.allFrags)
      let Sr := S.filter (· ∈ r.allFrags)
      let L := S.filter (fun F ↦ F ∉ l.allFrags ∧ F ∉ r.allFrags)
      let sl := coverMask Sl l.bag
      let sr := coverMask Sr r.bag
      have hchildren := NTD.join_decompose
        (.join hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr) hS
      have hleft : SubFeasible l sl Sl := hchildren.1
      have hright : SubFeasible r sr Sr := hchildren.2
      have hleftmem : (sl, Sl) ∈ l.solutionTable := ihl hleft
      have hrightmem : (sr, Sr) ∈ r.solutionTable := ihr hright
      have hL : L ⊆ lf := by
        intro F hF
        have hFS := (Finset.mem_filter.mp hF).1
        obtain ⟨hFnotl, hFnotr⟩ := (Finset.mem_filter.mp hF).2
        have hFall := hS.1 hFS
        simp only [NTD.allFrags, Finset.mem_union] at hFall
        rcases hFall with (hFlf | hFl) | hFr
        · exact hFlf
        · exact absurd hFl hFnotl
        · exact absurd hFr hFnotr
      have hsplit : L ∪ Sl ∪ Sr = S := by
        ext F
        simp only [L, Sl, Sr, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro ((⟨hF, -, -⟩ | ⟨hF, -⟩) | ⟨hF, -⟩)
          · exact hF
          · exact hF
          · exact hF
        · intro hF
          by_cases hFl : F ∈ l.allFrags
          · exact Or.inl (Or.inr ⟨hF, hFl⟩)
          · by_cases hFr : F ∈ r.allFrags
            · exact Or.inr ⟨hF, hFr⟩
            · exact Or.inl (Or.inl ⟨hF, hFl, hFr⟩)
      have hmask : coverMask S l.bag = s := by
        simpa only [NTD.bag] using hS.2.2
      simp only [NTD.solutionTable, Finset.mem_image]
      refine ⟨(L, (sl, Sl), sr, Sr), ?_, ?_⟩
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr hL, Finset.mem_product.mpr ⟨hleftmem, hrightmem⟩⟩
      · simp only
        rw [hsplit, hmask]

/-- Cardinalities of all exact recursive-table witnesses for mask `s`. -/
def NTD.costsFor (t : NTD α) (s : Finset α) : Finset ℕ :=
  (t.solutionTable.filter fun entry => entry.1 = s).image fun entry => entry.2.card

/-- Executable recursive optimum, with `⊤` explicitly representing an
    infeasible state. -/
def tauDPRec (t : NTD α) (s : Finset α) : WithTop ℕ :=
  (t.costsFor s).min

theorem NTD.mem_costsFor_iff {t : NTD α} {s : Finset α} {n : ℕ} :
    n ∈ t.costsFor s ↔
      ∃ S : Finset (Finset α), (s, S) ∈ t.solutionTable ∧ S.card = n := by
  simp only [NTD.costsFor, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨s', S⟩, ⟨hmem, hs⟩, hcard⟩
    simp only at hs hcard
    subst s'
    exact ⟨S, hmem, hcard⟩
  · rintro ⟨S, hmem, rfl⟩
    exact ⟨(s, S), ⟨hmem, rfl⟩, rfl⟩

/-- The executable recurrence returns `⊤` exactly for infeasible masks. -/
theorem tauDPRec_eq_top_iff {t : NTD α} (hWF : NTD.WF t) {s : Finset α} :
    tauDPRec t s = ⊤ ↔ ¬ ∃ S : Finset (Finset α), SubFeasible t s S := by
  rw [tauDPRec, Finset.min_eq_top]
  constructor
  · intro hempty
    rintro ⟨S, hS⟩
    have hcost : S.card ∈ t.costsFor s :=
      NTD.mem_costsFor_iff.mpr ⟨S, NTD.solutionTable_complete hWF hS, rfl⟩
    rw [hempty] at hcost
    exact Finset.notMem_empty _ hcost
  · intro hinfeasible
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨S, htable, -⟩ := NTD.mem_costsFor_iff.mp hn
    exact hinfeasible ⟨S, NTD.solutionTable_sound hWF htable⟩

/-- **Ingredient 3 (full tree induction)**: `DP[u,s] = OPT[u,s]` for every node kind.
    All four cases of the nice-decomposition induction are covered:
    leaf (base case), introduce, forget, and join.
    Each case provides both a completeness (assemble) and a soundness (decompose) direction,
    establishing that the `SubFeasible` predicate is exactly the bag-mask DP table. -/
theorem ingredient3_full :
    -- Leaf: only the empty selection is feasible
    (∀ {s : Finset α} {S : Finset (Finset α)},
       SubFeasible (.leaf : NTD α) s S ↔ S = ∅ ∧ s = ∅) ∧
    -- Introduce (completeness): child + local fragments assemble
    (∀ {a : α} {lf : Finset (Finset α)} {t : NTD α}
         {Sl Sc : Finset (Finset α)} {sc : Finset α},
       Sl ⊆ lf → SubFeasible t sc Sc →
       SubFeasible (.introduce a lf t) (coverMask (Sl ∪ Sc) (insert a t.bag)) (Sl ∪ Sc)) ∧
    -- Introduce (soundness): feasible selection restricts to child
    (∀ {a : α} {lf : Finset (Finset α)} {t : NTD α}
         {s : Finset α} {S : Finset (Finset α)},
       NTD.WF (.introduce a lf t) → SubFeasible (.introduce a lf t) s S →
       SubFeasible t (coverMask (S.filter (· ∈ t.allFrags)) t.bag)
                     (S.filter (· ∈ t.allFrags))) ∧
    -- Forget (completeness): child + local + atom-coverage assemble
    (∀ {a : α} {lf : Finset (Finset α)} {t : NTD α}
         {Sl Sc : Finset (Finset α)} {sc : Finset α},
       Sl ⊆ lf → SubFeasible t sc Sc → a ∈ (Sl ∪ Sc).biUnion id →
       SubFeasible (.forget a lf t) (coverMask (Sl ∪ Sc) (t.bag.erase a)) (Sl ∪ Sc)) ∧
    -- Forget (soundness): feasible selection restricts to child
    (∀ {a : α} {lf : Finset (Finset α)} {t : NTD α}
         {s : Finset α} {S : Finset (Finset α)},
       NTD.WF (.forget a lf t) → SubFeasible (.forget a lf t) s S →
       SubFeasible t (coverMask (S.filter (· ∈ t.allFrags)) t.bag)
                     (S.filter (· ∈ t.allFrags))) ∧
    -- Join (completeness): two child selections assemble
    (∀ {lf : Finset (Finset α)} {l r : NTD α} {sl sr : Finset α}
         {Sl Sr : Finset (Finset α)},
       NTD.WF (.join lf l r) → SubFeasible l sl Sl → SubFeasible r sr Sr →
       SubFeasible (.join lf l r) (sl ∪ sr) (Sl ∪ Sr)) ∧
    -- Join (soundness): feasible selection decomposes into two child selections
    (∀ {lf : Finset (Finset α)} {l r : NTD α} {s : Finset α} {S : Finset (Finset α)},
       NTD.WF (.join lf l r) → SubFeasible (.join lf l r) s S →
       SubFeasible l (coverMask (S.filter (· ∈ l.allFrags)) l.bag)
                     (S.filter (· ∈ l.allFrags)) ∧
       SubFeasible r (coverMask (S.filter (· ∈ r.allFrags)) r.bag)
                     (S.filter (· ∈ r.allFrags))) :=
  ⟨NTD.leaf_feasible,
   fun hSl hSc => NTD.introduce_assemble hSl hSc,
   fun hWF hS  => NTD.introduce_decompose hWF hS,
   fun hSl hSc ha => NTD.forget_assemble hSl hSc ha,
   fun hWF hS  => NTD.forget_decompose hWF hS,
   fun h hl hr => NTD.join_assemble h hl hr,
   fun h hS    => NTD.join_decompose h hS⟩

end TreeInduction

/-! ## Gap A: DP Minimum and τ Capstone

`tauDP t s` is the minimum cardinality of any subtree-feasible fragment
selection at node `t` for bag mask `s`.  Together with `tau_dp_eq_opt` and
`tau_capstone`, this closes the abstract half of the formalization: every
structural ingredient needed for the finite-state τ DP is in place and
with no proof placeholders.

Gap B (open in full universal generality, `docs/lean-formalization-plan.md`):
instantiate `ρ` and the fragment families to concrete normalized cells and
connect to an explicit definition of `τ(d_0)`. The cell-level PID theorem A
is now formalized separately in `WholeAxisPID.lean`. -/

section TauDP

variable {α : Type*} [DecidableEq α]

/-- Minimum cardinality of a subtree-feasible fragment selection at node `t`
    for bag mask `s`.  Set to `sInf ∅ = 0` when no feasible selection
    exists (infeasible mask). -/
noncomputable def tauDP (t : NTD α) (s : Finset α) : ℕ :=
  sInf {n | ∃ S : Finset (Finset α), SubFeasible t s S ∧ S.card = n}

/-- Every feasible selection is a certificate: `tauDP ≤ S.card`. -/
theorem tauDP_le_card {t : NTD α} {s : Finset α} {S : Finset (Finset α)}
    (hS : SubFeasible t s S) : tauDP t s ≤ S.card :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-- When a feasible selection exists the DP minimum is attained by some `S*`. -/
theorem tauDP_attained {t : NTD α} {s : Finset α}
    (h : ∃ S : Finset (Finset α), SubFeasible t s S) :
    ∃ S : Finset (Finset α), SubFeasible t s S ∧ S.card = tauDP t s := by
  obtain ⟨S, hS⟩ := h
  have hne : ({n | ∃ T : Finset (Finset α), SubFeasible t s T ∧ T.card = n} : Set ℕ).Nonempty :=
    ⟨S.card, S, hS, rfl⟩
  exact Nat.sInf_mem hne

/-- On every feasible state of a well-formed decomposition, the executable
    recurrence agrees with the semantic `sInf` definition of `tauDP`. -/
theorem tauDPRec_eq_coe_tauDP {t : NTD α} (hWF : NTD.WF t) {s : Finset α}
    (hfeasible : ∃ S : Finset (Finset α), SubFeasible t s S) :
    tauDPRec t s = (tauDP t s : WithTop ℕ) := by
  obtain ⟨Sstar, hSstar, hcardstar⟩ := tauDP_attained hfeasible
  have hcoststar : tauDP t s ∈ t.costsFor s := by
    apply NTD.mem_costsFor_iff.mpr
    exact ⟨Sstar, NTD.solutionTable_complete hWF hSstar, hcardstar⟩
  have hnonempty : (t.costsFor s).Nonempty := ⟨tauDP t s, hcoststar⟩
  rw [tauDPRec, ← Finset.coe_min' hnonempty]
  apply le_antisymm
  · exact WithTop.coe_le_coe.mpr (Finset.min'_le _ _ hcoststar)
  · obtain ⟨S, htable, hcard⟩ :=
      NTD.mem_costsFor_iff.mp (Finset.min'_mem (t.costsFor s) hnonempty)
    rw [← hcard]
    exact WithTop.coe_le_coe.mpr (tauDP_le_card (NTD.solutionTable_sound hWF htable))

/-- Full characterization of the executable recurrence: it is the semantic
    optimum on feasible states and `⊤` exactly otherwise. -/
theorem tauDPRec_characterization {t : NTD α} (hWF : NTD.WF t) {s : Finset α} :
    (tauDPRec t s = ⊤ ↔
      ¬ ∃ S : Finset (Finset α), SubFeasible t s S) ∧
    ((∃ S : Finset (Finset α), SubFeasible t s S) →
      tauDPRec t s = (tauDP t s : WithTop ℕ)) :=
  ⟨tauDPRec_eq_top_iff hWF, tauDPRec_eq_coe_tauDP hWF⟩

/-! ### Cost-only recursive table

`solutionTable` retains a full fragment selection in every row.  The recurrence
below stores only a bag mask and its cardinality.  Its soundness and completeness
theorems show that this compression preserves the exact optimum. -/

/-- Cost-only recurrence rows. Multiple rows may share a mask; `costDP` takes
    their minimum. -/
def NTD.costRows : NTD α → Finset (Finset α × ℕ)
  | .leaf => {(∅, 0)}
  | .introduce a lf t =>
      ((t.freshLocal lf).powerset ×ˢ t.costRows).image fun entry =>
        let L := entry.1
        let child := entry.2
        (coverMask L (insert a t.bag) ∪ child.1, L.card + child.2)
  | .forget a lf t =>
      (((t.freshLocal lf).powerset ×ˢ t.costRows).filter fun entry =>
        a ∈ entry.2.1).image fun entry =>
          let L := entry.1
          let child := entry.2
          let parentBag := t.bag.erase a
          (coverMask L parentBag ∪ (child.1 ∩ parentBag), L.card + child.2)
  | .join lf l r =>
      (lf.powerset ×ˢ (l.costRows ×ˢ r.costRows)).image fun entry =>
        let L := entry.1
        let left := entry.2.1
        let right := entry.2.2
        (coverMask L l.bag ∪ left.1 ∪ right.1, L.card + left.2 + right.2)

/-- Minimum cost retained by the cost-only recurrence, with `⊤` for a mask
    having no row. -/
def costDP (t : NTD α) (s : Finset α) : WithTop ℕ :=
  ((t.costRows.filter fun entry => entry.1 = s).image fun entry => entry.2).min

private theorem coverMask_union_cost (S T : Finset (Finset α)) (B : Finset α) :
    coverMask (S ∪ T) B = coverMask S B ∪ coverMask T B := by
  have hbiUnion : (S ∪ T).biUnion id = S.biUnion id ∪ T.biUnion id := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_union, id]
    constructor
    · rintro ⟨F, hF | hF, hx⟩
      · exact Or.inl ⟨F, hF, hx⟩
      · exact Or.inr ⟨F, hF, hx⟩
    · rintro (⟨F, hF, hx⟩ | ⟨F, hF, hx⟩)
      · exact ⟨F, Or.inl hF, hx⟩
      · exact ⟨F, Or.inr hF, hx⟩
  simp only [coverMask, hbiUnion, Finset.union_inter_distrib_right]

private theorem coverMask_child_at_introduce {a : α} {lf : Finset (Finset α)}
    {t : NTD α} (hWF : NTD.WF (.introduce a lf t)) {sc : Finset α}
    {S : Finset (Finset α)} (hS : SubFeasible t sc S) :
    coverMask S (insert a t.bag) = sc := by
  cases hWF with
  | introduce ha_bag ha_int hlf_sub ht =>
      have ha_not : a ∉ S.biUnion id := by
        intro ha
        obtain ⟨F, hFS, haF⟩ := Finset.mem_biUnion.mp ha
        have hsupport := ht.allFrags_subset_bag_union_interior F (hS.1 hFS) haF
        rcases Finset.mem_union.mp hsupport with h | h
        · exact ha_bag h
        · exact ha_int h
      calc
        coverMask S (insert a t.bag) = coverMask S t.bag := by
          ext x
          simp [coverMask, ha_not]
        _ = sc := hS.2.2

private theorem coverMask_child_at_forget {a : α} {t : NTD α}
    {sc : Finset α} {S : Finset (Finset α)} (hS : SubFeasible t sc S) :
    coverMask S (t.bag.erase a) = sc ∩ t.bag.erase a := by
  rw [← hS.2.2]
  ext x
  simp [coverMask]

private theorem SubFeasible.add_left_cost {t : NTD α} {s : Finset α}
    {S L : Finset (Finset α)} (hS : SubFeasible t s S) (hL : L ⊆ t.allFrags) :
    SubFeasible t (coverMask (L ∪ S) t.bag) (L ∪ S) := by
  refine ⟨Finset.union_subset hL hS.1, ?_, rfl⟩
  exact hS.2.1.trans fun x hx ↦
    let ⟨F, hFS, hxF⟩ := Finset.mem_biUnion.mp hx
    Finset.mem_biUnion.mpr ⟨F, Finset.mem_union_right _ hFS, hxF⟩

/-- Every row generated by the cost-only recurrence has a feasible witness of
    exactly the recorded cardinality. -/
theorem NTD.costRows_sound {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} {n : ℕ} (hmem : (s, n) ∈ t.costRows) :
    ∃ S : Finset (Finset α), SubFeasible t s S ∧ S.card = n := by
  induction hWF generalizing s n with
  | leaf =>
      simp only [NTD.costRows, Finset.mem_singleton, Prod.mk.injEq] at hmem
      exact ⟨∅, NTD.leaf_feasible.mpr ⟨rfl, hmem.1⟩, hmem.2.symm⟩
  | @introduce a lf t ha_bag ha_int hlf_sub ht ih =>
      simp only [NTD.costRows, Finset.mem_image, Finset.mem_product,
        Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, sc, nc⟩, ⟨hL, hchild⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hn
      subst s
      subst n
      obtain ⟨Sc, hSc, hcard⟩ := ih hchild
      have hparent := NTD.introduce_assemble (a := a)
        (hL.trans Finset.sdiff_subset) hSc
      have hmask :
          coverMask (L ∪ Sc) (insert a t.bag) =
            coverMask L (insert a t.bag) ∪ sc := by
        rw [coverMask_union_cost, coverMask_child_at_introduce
          (.introduce ha_bag ha_int hlf_sub ht) hSc]
      rw [hmask] at hparent
      have hdisj : Disjoint L Sc := by
        refine Finset.disjoint_left.mpr ?_
        intro F hFL hFSc
        exact (Finset.mem_sdiff.mp (hL hFL)).2 (hSc.1 hFSc)
      refine ⟨L ∪ Sc, hparent, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hcard]
  | @forget a lf t ha hlf_sub ht ih =>
      simp only [NTD.costRows, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product, Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, sc, nc⟩, ⟨⟨hL, hchild⟩, ha_sc⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hn
      subst s
      subst n
      obtain ⟨Sc, hSc, hcard⟩ := ih hchild
      have ha_mask : a ∈ coverMask Sc t.bag := hSc.2.2.symm ▸ ha_sc
      have ha_cov : a ∈ Sc.biUnion id := by
        exact (Finset.mem_inter.mp (by simpa only [coverMask] using ha_mask)).1
      have ha_union : a ∈ (L ∪ Sc).biUnion id := by
        obtain ⟨F, hF, haF⟩ := Finset.mem_biUnion.mp ha_cov
        exact Finset.mem_biUnion.mpr ⟨F, Finset.mem_union_right L hF, haF⟩
      have hparent := NTD.forget_assemble (hL.trans Finset.sdiff_subset) hSc
        ha_union
      have hmask :
          coverMask (L ∪ Sc) (t.bag.erase a) =
            coverMask L (t.bag.erase a) ∪ (sc ∩ t.bag.erase a) := by
        rw [coverMask_union_cost, coverMask_child_at_forget hSc]
      rw [hmask] at hparent
      have hdisj : Disjoint L Sc := by
        refine Finset.disjoint_left.mpr ?_
        intro F hFL hFSc
        exact (Finset.mem_sdiff.mp (hL hFL)).2 (hSc.1 hFSc)
      refine ⟨L ∪ Sc, hparent, ?_⟩
      rw [Finset.card_union_of_disjoint hdisj, hcard]
  | @join lf l r hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr ihl ihr =>
      simp only [NTD.costRows, Finset.mem_image, Finset.mem_product,
        Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, ⟨sl, nl⟩, sr, nr⟩, ⟨hL, hleft, hright⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hn
      subst s
      subst n
      obtain ⟨Sl, hSl, hcardl⟩ := ihl hleft
      obtain ⟨Sr, hSr, hcardr⟩ := ihr hright
      have hjoinWF : NTD.WF (.join lf l r) :=
        .join hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr
      have hchildren := NTD.join_assemble hjoinWF hSl hSr
      have hlocal : L ⊆ (NTD.join lf l r).allFrags := by
        intro F hF
        simp only [NTD.allFrags, Finset.mem_union]
        exact Or.inl (Or.inl (hL hF))
      have hparent := hchildren.add_left_cost hlocal
      have hchildrenMask : coverMask (Sl ∪ Sr) l.bag = sl ∪ sr := by
        simpa only [NTD.bag] using hchildren.2.2
      have hmask : coverMask (L ∪ (Sl ∪ Sr)) (NTD.join lf l r).bag =
          coverMask L l.bag ∪ sl ∪ sr := by
        change coverMask (L ∪ (Sl ∪ Sr)) l.bag = _
        rw [coverMask_union_cost, hchildrenMask]
        simp only [Finset.union_assoc]
      rw [hmask] at hparent
      have hdisjChildren : Disjoint Sl Sr := hd.mono hSl.1 hSr.1
      have hchildrenSub : Sl ∪ Sr ⊆ l.allFrags ∪ r.allFrags :=
        Finset.union_subset (hSl.1.trans Finset.subset_union_left)
          (hSr.1.trans Finset.subset_union_right)
      have hdisjLocal : Disjoint L (Sl ∪ Sr) :=
        hlf_disj.mono hL hchildrenSub
      refine ⟨L ∪ (Sl ∪ Sr), hparent, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisjLocal,
          Finset.card_union_of_disjoint hdisjChildren, hcardl, hcardr]
        omega

private theorem NTD.costRows_of_solutionTable {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} {S : Finset (Finset α)}
    (hmem : (s, S) ∈ t.solutionTable) : (s, S.card) ∈ t.costRows := by
  induction hWF generalizing s S with
  | leaf =>
      simpa [NTD.solutionTable, NTD.costRows] using hmem
  | @introduce a lf t ha_bag ha_int hlf_sub ht ih =>
      simp only [NTD.solutionTable, Finset.mem_image, Finset.mem_product,
        Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, sc, Sc⟩, ⟨hL, hchild⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hS
      subst s
      subst S
      have hchildCost := ih hchild
      have hSc := NTD.solutionTable_sound ht hchild
      have hmask :
          coverMask (L ∪ Sc) (insert a t.bag) =
            coverMask L (insert a t.bag) ∪ sc := by
        rw [coverMask_union_cost, coverMask_child_at_introduce
          (.introduce ha_bag ha_int hlf_sub ht) hSc]
      have hdisj : Disjoint L Sc := by
        refine Finset.disjoint_left.mpr ?_
        intro F hFL hFSc
        exact (Finset.mem_sdiff.mp (hL hFL)).2 (hSc.1 hFSc)
      have hcard : (L ∪ Sc).card = L.card + Sc.card :=
        Finset.card_union_of_disjoint hdisj
      simp only [NTD.costRows, Finset.mem_image]
      refine ⟨(L, sc, Sc.card), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hL, hchildCost⟩
      · simp only
        rw [← hmask, ← hcard]
  | @forget a lf t ha hlf_sub ht ih =>
      simp only [NTD.solutionTable, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product, Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, sc, Sc⟩, ⟨⟨hL, hchild⟩, ha_cov⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hS
      subst s
      subst S
      have hchildCost := ih hchild
      have hSc := NTD.solutionTable_sound ht hchild
      have ha_sc : a ∈ sc := by
        obtain ⟨F, hF, haF⟩ := Finset.mem_biUnion.mp ha_cov
        rcases Finset.mem_union.mp hF with hFL | hFSc
        · have hFsub := hlf_sub F (Finset.mem_sdiff.mp (hL hFL)).1
          have ha_not : a ∉ t.bag.erase a := by simp
          exact (ha_not (hFsub haF)).elim
        · rw [← hSc.2.2]
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_biUnion.mpr ⟨F, hFSc, haF⟩, ha⟩
      have hmask :
          coverMask (L ∪ Sc) (t.bag.erase a) =
            coverMask L (t.bag.erase a) ∪ (sc ∩ t.bag.erase a) := by
        rw [coverMask_union_cost, coverMask_child_at_forget hSc]
      have hdisj : Disjoint L Sc := by
        refine Finset.disjoint_left.mpr ?_
        intro F hFL hFSc
        exact (Finset.mem_sdiff.mp (hL hFL)).2 (hSc.1 hFSc)
      have hcard : (L ∪ Sc).card = L.card + Sc.card :=
        Finset.card_union_of_disjoint hdisj
      simp only [NTD.costRows, Finset.mem_image]
      refine ⟨(L, sc, Sc.card), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hL, hchildCost⟩, ha_sc⟩
      · simp only
        rw [← hmask, ← hcard]
  | @join lf l r hbag hd hlf_sub hlf_disj hsep_l hsep_r hl hr ihl ihr =>
      simp only [NTD.solutionTable, Finset.mem_image, Finset.mem_product,
        Finset.mem_powerset] at hmem
      rcases hmem with ⟨⟨L, ⟨sl, Sl⟩, sr, Sr⟩, ⟨hL, hleft, hright⟩, hEq⟩
      simp only at hEq
      injection hEq with hs hS
      subst s
      subst S
      have hleftCost := ihl hleft
      have hrightCost := ihr hright
      have hSl := NTD.solutionTable_sound hl hleft
      have hSr := NTD.solutionTable_sound hr hright
      have hSrMask : coverMask Sr l.bag = sr := by
        rw [hbag]
        exact hSr.2.2
      have hmask : coverMask (L ∪ Sl ∪ Sr) l.bag =
          coverMask L l.bag ∪ sl ∪ sr := by
        rw [coverMask_union_cost, coverMask_union_cost, hSl.2.2, hSrMask]
      have hdisjChildren : Disjoint Sl Sr := hd.mono hSl.1 hSr.1
      have hchildrenSub : Sl ∪ Sr ⊆ l.allFrags ∪ r.allFrags :=
        Finset.union_subset (hSl.1.trans Finset.subset_union_left)
          (hSr.1.trans Finset.subset_union_right)
      have hdisjLocal : Disjoint L (Sl ∪ Sr) :=
        hlf_disj.mono hL hchildrenSub
      have hcard : (L ∪ Sl ∪ Sr).card = L.card + Sl.card + Sr.card := by
        rw [Finset.union_assoc, Finset.card_union_of_disjoint hdisjLocal,
          Finset.card_union_of_disjoint hdisjChildren]
        omega
      simp only [NTD.costRows, Finset.mem_image]
      refine ⟨(L, (sl, Sl.card), sr, Sr.card), ?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hL,
          Finset.mem_product.mpr ⟨hleftCost, hrightCost⟩⟩
      · simp only
        rw [← hmask, ← hcard]

/-- Every semantically feasible selection contributes its cardinality to the
    cost-only table. -/
theorem NTD.costRows_complete {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} {S : Finset (Finset α)} (hS : SubFeasible t s S) :
    (s, S.card) ∈ t.costRows :=
  NTD.costRows_of_solutionTable hWF (NTD.solutionTable_complete hWF hS)

/-- A cost-only row is present exactly when some feasible selection has that
    cardinality. -/
theorem NTD.mem_costRows_iff {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} {n : ℕ} :
    (s, n) ∈ t.costRows ↔
      ∃ S : Finset (Finset α), SubFeasible t s S ∧ S.card = n := by
  constructor
  · exact fun h ↦ NTD.costRows_sound hWF h
  · rintro ⟨S, hS, rfl⟩
    exact NTD.costRows_complete hWF hS

private theorem NTD.costRows_values_eq_costsFor {t : NTD α} (hWF : NTD.WF t)
    {s : Finset α} :
    ((t.costRows.filter fun entry => entry.1 = s).image fun entry => entry.2) =
      t.costsFor s := by
  ext n
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨s', n'⟩, ⟨hrow, hs⟩, hn⟩
    simp only at hs hn
    subst s'
    subst n'
    obtain ⟨S, hS, hcard⟩ := NTD.costRows_sound hWF hrow
    exact NTD.mem_costsFor_iff.mpr
      ⟨S, NTD.solutionTable_complete hWF hS, hcard⟩
  · intro hn
    obtain ⟨S, htable, hcard⟩ := NTD.mem_costsFor_iff.mp hn
    refine ⟨(s, S.card), ⟨NTD.costRows_complete hWF
      (NTD.solutionTable_sound hWF htable), rfl⟩, hcard⟩

/-- The cost-only recurrence preserves the exact optimum of `tauDPRec` on
    every well-formed decomposition. -/
theorem costDP_eq_tauDPRec {t : NTD α} (hWF : NTD.WF t) {s : Finset α} :
    costDP t s = tauDPRec t s := by
  rw [costDP, tauDPRec, NTD.costRows_values_eq_costsFor hWF]

/-- **DP exact**: the minimum is simultaneously a lower bound for every
    feasible selection and is itself attained.  Combines soundness
    (`tauDP_le_card`) and completeness (`tauDP_attained`). -/
theorem tau_dp_eq_opt {t : NTD α} {s : Finset α}
    (h : ∃ S : Finset (Finset α), SubFeasible t s S) :
    (∃ S : Finset (Finset α), SubFeasible t s S ∧ S.card = tauDP t s) ∧
    ∀ S : Finset (Finset α), SubFeasible t s S → tauDP t s ≤ S.card :=
  ⟨tauDP_attained h, fun S hS => tauDP_le_card hS⟩

/-- Leaf base case of the DP: only the empty mask is feasible and
    `tauDP (.leaf) ∅ = 0`.  Uses the standalone `NTD.leaf_feasible` (which
    `ingredient3_full` also re-exports). -/
theorem tauDP_leaf_empty : tauDP (.leaf : NTD α) ∅ = 0 :=
  Nat.le_zero.mp (tauDP_le_card (NTD.leaf_feasible.mpr ⟨rfl, rfl⟩))

/-- **τ capstone (Gap A)**: every structural ingredient needed for the
    finite-state τ DP is in place.

    Proved in this file (all without proof placeholders):
    - `ingredient1`: fragment membership constant on atoms; atom signatures
      injective; `atomClass` equality is exactly atom-equivalence
      (coarsestness is the separate `atomization_is_coarsest`)
    - `ingredient2a`: every atom pair is jointly contained in their LCA bag
    - `ingredient2b`: `|frontierBag ρ u| ≤ 1 + n₂ + n₅ + n₁₁` under
      rail-wise local injectivity
    - `ingredient3_lite`: interface congruence + 2^|B| bag-state bound
    - `ingredient3_full`: `DP[u,s]=OPT[u,s]` for leaf/introduce/forget/join
    - `tauDP_le_card`: DP lower-bounds every feasible selection (soundness)
    - `tauDP_attained`: the DP minimum is attained (completeness)

    Gap B (open): instantiate the local/frontier ρ and the fragment families
    to concrete normalized cells; define `τ(d_0)` explicitly; connect via
    `tauDP root ∅`. -/
theorem tau_capstone :
    -- I1: atom signatures are injective
    (∀ (F : ι → Finset α), Function.Injective (signatureQuot F)) ∧
    -- I2a: every atom pair shares an LCA signature bag
    (∀ (σ : α → ι → Bool) (x y : α),
       x ∈ sigBag σ (sigLCA (fullPartialSig σ x) (fullPartialSig σ y)) ∧
       y ∈ sigBag σ (sigLCA (fullPartialSig σ x) (fullPartialSig σ y))) ∧
    -- I3 sound: tauDP ≤ every feasible selection
    (∀ (t : NTD α) (s : Finset α) (S : Finset (Finset α)),
       SubFeasible t s S → tauDP t s ≤ S.card) ∧
    -- I3 complete: DP minimum is attained when any feasible selection exists
    (∀ (t : NTD α) (s : Finset α),
       (∃ S : Finset (Finset α), SubFeasible t s S) →
       ∃ S : Finset (Finset α), SubFeasible t s S ∧ S.card = tauDP t s) :=
  ⟨fun F  => (ingredient1 F).2.1,
   fun σ x y => (ingredient2a σ).2.2.1 x y,
   fun _ _ _ hS => tauDP_le_card hS,
   fun _ _ h  => tauDP_attained h⟩

end TauDP

/-! ## Gap B1: Concrete minimum-cover `τ`

`tau frags` = minimum number of fragments from `frags` whose union
contains all atoms covered by `frags`.  `minCoverExists` witnesses that
the full collection covers itself, making the `sInf` set nonempty. -/

section ConcreteCover

variable {α : Type*} [DecidableEq α]

/-- `S` is a cover of `frags` if `S ⊆ frags` and `S.biUnion id` contains
    every atom in `frags.biUnion id`. -/
def IsCoverOf (frags S : Finset (Finset α)) : Prop :=
  S ⊆ frags ∧ frags.biUnion id ⊆ S.biUnion id

/-- The full collection trivially covers itself. -/
theorem minCoverExists (frags : Finset (Finset α)) :
    ∃ n : ℕ, ∃ S : Finset (Finset α), IsCoverOf frags S ∧ S.card = n :=
  ⟨frags.card, frags, ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩, rfl⟩

/-- Minimum cardinality of a cover of `frags`.
    Uses `sInf` (like `tauDP`) so the same `Nat.sInf_le`/`Nat.sInf_mem` API applies. -/
noncomputable def tau (frags : Finset (Finset α)) : ℕ :=
  sInf {n | ∃ S : Finset (Finset α), IsCoverOf frags S ∧ S.card = n}

theorem tau_le_card (frags : Finset (Finset α)) : tau frags ≤ frags.card :=
  Nat.sInf_le ⟨frags, ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩, rfl⟩

/-- At an empty root bag, subtree feasibility is exactly ordinary cover
    feasibility when the NTD interior and fragment family match `frags`. -/
theorem subFeasible_empty_iff_isCoverOf {t : NTD α} {frags S : Finset (Finset α)}
    (hbag : t.bag = ∅) (hinterior : t.interior = frags.biUnion id)
    (hallFrags : t.allFrags = frags) :
    SubFeasible t ∅ S ↔ IsCoverOf frags S := by
  simp [SubFeasible, Feasible, IsCoverOf, hbag, hinterior, hallFrags, coverMask]

/-- The semantic NTD optimum at an empty root is the concrete minimum-cover
    number when the root records exactly the supplied fragment family and its
    covered atom set. -/
theorem tauDP_eq_tau_of_root {t : NTD α} {frags : Finset (Finset α)}
    (hbag : t.bag = ∅) (hinterior : t.interior = frags.biUnion id)
    (hallFrags : t.allFrags = frags) :
    tauDP t ∅ = tau frags := by
  apply congrArg sInf
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨S, hS, hcard⟩
    exact ⟨S, (subFeasible_empty_iff_isCoverOf hbag hinterior hallFrags).mp hS, hcard⟩
  · rintro ⟨S, hS, hcard⟩
    exact ⟨S, (subFeasible_empty_iff_isCoverOf hbag hinterior hallFrags).mpr hS, hcard⟩

end ConcreteCover

/-! ## Gap B2: Fragment family for d₀ = 440

45 maximal residual fragments for the normalized n=220 cell d₀=440.
Each fragment is a subset of residues in {1,…,219} ⊂ ZMod 440,
computed from `stable_candidate_masks(96800, 441)` restricted to the
residual mask (positions not forced by the stable certificate).

Positions are 1-indexed residues in ℤ/220ℤ, embedded in ZMod 440
as the same numeric value (all < 440). -/

section ConcreteFrags440

def frags_440 : Finset (Finset (ZMod 440)) := {
  ({15, 31, 47, 95, 111, 127, 143, 159, 175} : Finset (ZMod 440)),
  ({2, 27, 52, 77, 102, 127, 152, 177, 202} : Finset (ZMod 440)),
  ({11, 27, 43, 75, 123, 139, 155, 171, 203} : Finset (ZMod 440)),
  ({45, 61, 77, 93, 109, 125, 173, 189, 205} : Finset (ZMod 440)),
  ({17, 49, 65, 81, 97, 145, 177, 193, 209} : Finset (ZMod 440)),
  ({18, 43, 68, 93, 118, 143, 168, 193, 218} : Finset (ZMod 440)),
  ({11, 36, 61, 86, 111, 136, 186} : Finset (ZMod 440)),
  ({34, 84, 109, 134, 159, 184, 209} : Finset (ZMod 440)),
  ({6, 31, 56, 81, 106, 156} : Finset (ZMod 440)),
  ({22, 47, 72, 97, 122, 172} : Finset (ZMod 440)),
  ({48, 98, 123, 148, 173, 198} : Finset (ZMod 440)),
  ({10, 42, 74, 106, 170, 202} : Finset (ZMod 440)),
  ({18, 50, 114, 146, 178, 210} : Finset (ZMod 440)),
  ({64, 114, 139, 164, 189, 214} : Finset (ZMod 440)),
  ({6, 70, 102, 134, 198} : Finset (ZMod 440)),
  ({22, 86, 118, 150, 214} : Finset (ZMod 440)),
  ({24, 49, 74, 124} : Finset (ZMod 440)),
  ({2, 34, 98, 130} : Finset (ZMod 440)),
  ({17, 42, 92, 192} : Finset (ZMod 440)),
  ({96, 146, 171, 196} : Finset (ZMod 440)),
  ({28, 128, 178, 203} : Finset (ZMod 440)),
  ({90, 122, 186, 218} : Finset (ZMod 440)),
  ({2, 123} : Finset (ZMod 440)),
  ({6, 127} : Finset (ZMod 440)),
  ({15, 136} : Finset (ZMod 440)),
  ({18, 139} : Finset (ZMod 440)),
  ({24, 145} : Finset (ZMod 440)),
  ({27, 148} : Finset (ZMod 440)),
  ({31, 152} : Finset (ZMod 440)),
  ({34, 155} : Finset (ZMod 440)),
  ({43, 164} : Finset (ZMod 440)),
  ({47, 168} : Finset (ZMod 440)),
  ({49, 170} : Finset (ZMod 440)),
  ({50, 171} : Finset (ZMod 440)),
  ({52, 173} : Finset (ZMod 440)),
  ({56, 177} : Finset (ZMod 440)),
  ({65, 186} : Finset (ZMod 440)),
  ({68, 189} : Finset (ZMod 440)),
  ({30, 190} : Finset (ZMod 440)),
  ({72, 193} : Finset (ZMod 440)),
  ({75, 196} : Finset (ZMod 440)),
  ({81, 202} : Finset (ZMod 440)),
  ({84, 205} : Finset (ZMod 440)),
  ({93, 214} : Finset (ZMod 440)),
  ({97, 218} : Finset (ZMod 440))
}

set_option maxRecDepth 10000 in
/-- The `d₀ = 440` residual family has 45 maximal fragments (which between them
cover 92 residual positions). -/
theorem frags_440_card : frags_440.card = 45 := by decide

end ConcreteFrags440

/-! ## Gap B3: Canonical ρ for d₀ = 440 and injectivity (2bB)

`rho_440` maps each of the 87 atoms of d₀=440 to a coordinate in
`Fin 8 × Fin 4 × Fin 3`.  The arithmetic embedding `i ↦ (i/12, i%12/3, i%3)`
is injective on {0,…,86} ⊂ {0,…,95} = Fin 8 × Fin 4 × Fin 3.

`ingredient2b_of_injective rho_440 rho_440_injective` then gives
`(frontierBag rho_440 u).card ≤ 1 + 8 + 4 + 3 = 16` for every bag node u,
which is the treewidth-15 bag-size bound for d₀=440. -/

section ConcreteRho440

/-- Coordinate map for 87 atoms of d₀=440.
    Injective since 8·12 = 96 > 87 and the encoding i = 12·(i/12) + 3·((i%12)/3) + i%3
    is a bijection on {0,…,95}. -/
def rho_440 (i : Fin 87) : Fin 8 × Fin 4 × Fin 3 :=
  ⟨⟨i.val / 12, by omega⟩, ⟨(i.val % 12) / 3, by omega⟩, ⟨i.val % 3, by omega⟩⟩

theorem rho_440_injective : Function.Injective rho_440 := by decide

/-- **Bag-size bound for d₀=440**: every frontier bag has at most 16 atoms.
    Direct application of `ingredient2b_of_injective` with `n₂=8, n₅=4, n₁₁=3`. -/
theorem frontierBag_card_440 (u : Fin 8 × Fin 4 × Fin 3) :
    (frontierBag rho_440 u).card ≤ 16 :=
  (ingredient2b_of_injective rho_440 rho_440_injective).2.2.2.2.2.2 u

end ConcreteRho440

/-! ## Gap B5: Concrete tau upper bound for d₀ = 440

Proves `tau frags_440 ≤ 23` by exhibiting an explicit 23-fragment cover.
Uses `decide` (kernel reduction) rather than compiler-backed reduction to avoid
OOM. -/

section ConcreteTau440

/-- Optimal 23-fragment cover of frags_440. -/
def cover_440 : Finset (Finset (ZMod 440)) :=
  {({2, 27, 52, 77, 102, 127, 152, 177, 202} : Finset (ZMod 440)),
   ({11, 27, 43, 75, 123, 139, 155, 171, 203} : Finset (ZMod 440)),
   ({15, 31, 47, 95, 111, 127, 143, 159, 175} : Finset (ZMod 440)),
   ({17, 49, 65, 81, 97, 145, 177, 193, 209} : Finset (ZMod 440)),
   ({18, 43, 68, 93, 118, 143, 168, 193, 218} : Finset (ZMod 440)),
   ({45, 61, 77, 93, 109, 125, 173, 189, 205} : Finset (ZMod 440)),
   ({11, 36, 61, 86, 111, 136, 186} : Finset (ZMod 440)),
   ({34, 84, 109, 134, 159, 184, 209} : Finset (ZMod 440)),
   ({6, 31, 56, 81, 106, 156} : Finset (ZMod 440)),
   ({10, 42, 74, 106, 170, 202} : Finset (ZMod 440)),
   ({18, 50, 114, 146, 178, 210} : Finset (ZMod 440)),
   ({22, 47, 72, 97, 122, 172} : Finset (ZMod 440)),
   ({48, 98, 123, 148, 173, 198} : Finset (ZMod 440)),
   ({64, 114, 139, 164, 189, 214} : Finset (ZMod 440)),
   ({6, 70, 102, 134, 198} : Finset (ZMod 440)),
   ({22, 86, 118, 150, 214} : Finset (ZMod 440)),
   ({2, 34, 98, 130} : Finset (ZMod 440)),
   ({17, 42, 92, 192} : Finset (ZMod 440)),
   ({24, 49, 74, 124} : Finset (ZMod 440)),
   ({28, 128, 178, 203} : Finset (ZMod 440)),
   ({90, 122, 186, 218} : Finset (ZMod 440)),
   ({96, 146, 171, 196} : Finset (ZMod 440)),
   ({30, 190} : Finset (ZMod 440))}

set_option maxRecDepth 2000 in
theorem cover_440_card : cover_440.card = 23 := by decide
set_option maxRecDepth 2000 in
theorem cover_440_is_cover : IsCoverOf frags_440 cover_440 :=
  ⟨by decide, by decide⟩

/-- `τ(440) ≤ 23`: the residual fragment family for d₀ = 440
    can be covered by 23 of its 45 maximal fragments. -/
theorem tau_440_le : tau frags_440 ≤ 23 :=
  calc tau frags_440 ≤ cover_440.card :=
          Nat.sInf_le ⟨cover_440, cover_440_is_cover, rfl⟩
       _ = 23 := cover_440_card

/-- Matching certificate: 23 atoms, no two in the same fragment of frags_440. -/
def cert_atoms_440 : Finset (ZMod 440) :=
  {24, 30, 50, 56, 64, 65, 70, 72, 75, 90, 92, 95, 96, 128, 130, 136, 148, 150, 152, 168, 170, 184, 205}

set_option maxRecDepth 10000 in
theorem cert_atoms_440_card : cert_atoms_440.card = 23 := by decide

set_option maxRecDepth 10000 in
theorem cert_440_in_frags : cert_atoms_440 ⊆ frags_440.biUnion id := by decide

set_option maxRecDepth 10000 in
theorem cert_440_matching : ∀ f ∈ frags_440, (cert_atoms_440 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 10000 in
/-- `23 ≤ τ(440)`: any cover needs ≥ 23 fragments, witnessed by 23 atoms
    that form a matching (no two in the same fragment). -/
theorem tau_440_ge : 23 ≤ tau frags_440 := by
  unfold tau
  apply le_csInf (minCoverExists frags_440)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_440_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_440 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_440_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_440_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_440_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_440_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_440_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_440_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_440_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(440) = 23`. -/
theorem tau_440_eq : tau frags_440 = 23 := le_antisymm tau_440_le tau_440_ge

end ConcreteTau440

/-! ## Concrete τ for d₀ = 110 -/

section ConcreteTau110

/-- Maximal residual fragments for d₀ = 110. -/
def frags_110 : Finset (Finset (ZMod 220)) :=
  {({2, 10, 18, 34, 42, 50, 74, 90, 98, 106, 114, 122, 130, 146, 170, 178, 186, 202, 210, 218} : Finset (ZMod 220)),
   ({2, 52, 152, 202} : Finset (ZMod 220)),
   ({18, 68, 168, 218} : Finset (ZMod 220)),
   ({24, 74, 124} : Finset (ZMod 220)),
   ({48, 98, 148} : Finset (ZMod 220)),
   ({56, 106, 156} : Finset (ZMod 220)),
   ({64, 114, 164} : Finset (ZMod 220)),
   ({72, 122, 172} : Finset (ZMod 220)),
   ({28, 128, 178} : Finset (ZMod 220)),
   ({34, 84, 184} : Finset (ZMod 220)),
   ({36, 136, 186} : Finset (ZMod 220)),
   ({42, 92, 192} : Finset (ZMod 220)),
   ({96, 146, 196} : Finset (ZMod 220))}

/-- Optimal 13-fragment cover of frags_110. -/
def cover_110 : Finset (Finset (ZMod 220)) :=
  {({2, 10, 18, 34, 42, 50, 74, 90, 98, 106, 114, 122, 130, 146, 170, 178, 186, 202, 210, 218} : Finset (ZMod 220)),
   ({2, 52, 152, 202} : Finset (ZMod 220)),
   ({18, 68, 168, 218} : Finset (ZMod 220)),
   ({24, 74, 124} : Finset (ZMod 220)),
   ({48, 98, 148} : Finset (ZMod 220)),
   ({56, 106, 156} : Finset (ZMod 220)),
   ({64, 114, 164} : Finset (ZMod 220)),
   ({72, 122, 172} : Finset (ZMod 220)),
   ({28, 128, 178} : Finset (ZMod 220)),
   ({34, 84, 184} : Finset (ZMod 220)),
   ({36, 136, 186} : Finset (ZMod 220)),
   ({42, 92, 192} : Finset (ZMod 220)),
   ({96, 146, 196} : Finset (ZMod 220))}

set_option maxRecDepth 2000 in
theorem cover_110_card : cover_110.card = 13 := by decide
set_option maxRecDepth 2000 in
theorem cover_110_is_cover : IsCoverOf frags_110 cover_110 :=
  ⟨by decide, by decide⟩

/-- `τ(110) ≤ 13` -/
theorem tau_110_le : tau frags_110 ≤ 13 :=
  calc tau frags_110 ≤ cover_110.card :=
          Nat.sInf_le ⟨cover_110, cover_110_is_cover, rfl⟩
       _ = 13 := cover_110_card

/-- Matching certificate: 13 atoms, no two in the same fragment of frags_110. -/
def cert_atoms_110 : Finset (ZMod 220) :=
  {10, 24, 28, 36, 48, 52, 56, 64, 68, 72, 84, 92, 96}

set_option maxRecDepth 10000 in
theorem cert_atoms_110_card : cert_atoms_110.card = 13 := by decide

set_option maxRecDepth 10000 in
theorem cert_110_in_frags : cert_atoms_110 ⊆ frags_110.biUnion id := by decide

set_option maxRecDepth 10000 in
theorem cert_110_matching : ∀ f ∈ frags_110, (cert_atoms_110 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 10000 in
/-- `13 ≤ τ(110)`: matching certificate lower bound. -/
theorem tau_110_ge : 13 ≤ tau frags_110 := by
  unfold tau
  apply le_csInf (minCoverExists frags_110)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_110_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_110 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_110_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_110_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_110_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_110_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_110_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_110_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_110_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(110) = 13`. -/
theorem tau_110_eq : tau frags_110 = 13 := le_antisymm tau_110_le tau_110_ge

end ConcreteTau110

/-! ## Concrete τ for d₀ = 220 -/

section ConcreteTau220

/-- Maximal residual fragments for d₀ = 220. -/
def frags_220 : Finset (Finset (ZMod 220)) :=
  {({2, 18, 34, 50, 98, 114, 130, 146, 178, 210} : Finset (ZMod 220)),
   ({6, 22, 70, 86, 102, 118, 134, 150, 198, 214} : Finset (ZMod 220)),
   ({10, 42, 74, 90, 106, 122, 170, 186, 202, 218} : Finset (ZMod 220)),
   ({2, 52, 102, 152, 202} : Finset (ZMod 220)),
   ({18, 68, 118, 168, 218} : Finset (ZMod 220)),
   ({6, 56, 106, 156} : Finset (ZMod 220)),
   ({22, 72, 122, 172} : Finset (ZMod 220)),
   ({34, 84, 134, 184} : Finset (ZMod 220)),
   ({36, 86, 136, 186} : Finset (ZMod 220)),
   ({48, 98, 148, 198} : Finset (ZMod 220)),
   ({64, 114, 164, 214} : Finset (ZMod 220)),
   ({24, 74, 124} : Finset (ZMod 220)),
   ({28, 128, 178} : Finset (ZMod 220)),
   ({42, 92, 192} : Finset (ZMod 220)),
   ({96, 146, 196} : Finset (ZMod 220))}

/-- Optimal 15-fragment cover of frags_220. -/
def cover_220 : Finset (Finset (ZMod 220)) :=
  {({2, 18, 34, 50, 98, 114, 130, 146, 178, 210} : Finset (ZMod 220)),
   ({6, 22, 70, 86, 102, 118, 134, 150, 198, 214} : Finset (ZMod 220)),
   ({10, 42, 74, 90, 106, 122, 170, 186, 202, 218} : Finset (ZMod 220)),
   ({2, 52, 102, 152, 202} : Finset (ZMod 220)),
   ({18, 68, 118, 168, 218} : Finset (ZMod 220)),
   ({6, 56, 106, 156} : Finset (ZMod 220)),
   ({22, 72, 122, 172} : Finset (ZMod 220)),
   ({34, 84, 134, 184} : Finset (ZMod 220)),
   ({36, 86, 136, 186} : Finset (ZMod 220)),
   ({48, 98, 148, 198} : Finset (ZMod 220)),
   ({64, 114, 164, 214} : Finset (ZMod 220)),
   ({24, 74, 124} : Finset (ZMod 220)),
   ({28, 128, 178} : Finset (ZMod 220)),
   ({42, 92, 192} : Finset (ZMod 220)),
   ({96, 146, 196} : Finset (ZMod 220))}

set_option maxRecDepth 2000 in
theorem cover_220_card : cover_220.card = 15 := by decide
set_option maxRecDepth 2000 in
theorem cover_220_is_cover : IsCoverOf frags_220 cover_220 :=
  ⟨by decide, by decide⟩

/-- `τ(220) ≤ 15` -/
theorem tau_220_le : tau frags_220 ≤ 15 :=
  calc tau frags_220 ≤ cover_220.card :=
          Nat.sInf_le ⟨cover_220, cover_220_is_cover, rfl⟩
       _ = 15 := cover_220_card

/-- Matching certificate: 15 atoms, no two in the same fragment of frags_220. -/
def cert_atoms_220 : Finset (ZMod 220) :=
  {10, 24, 28, 36, 48, 50, 52, 56, 64, 68, 70, 72, 84, 92, 96}

set_option maxRecDepth 10000 in
theorem cert_atoms_220_card : cert_atoms_220.card = 15 := by decide

set_option maxRecDepth 10000 in
theorem cert_220_in_frags : cert_atoms_220 ⊆ frags_220.biUnion id := by decide

set_option maxRecDepth 10000 in
theorem cert_220_matching : ∀ f ∈ frags_220, (cert_atoms_220 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 10000 in
/-- `15 ≤ τ(220)`: matching certificate lower bound. -/
theorem tau_220_ge : 15 ≤ tau frags_220 := by
  unfold tau
  apply le_csInf (minCoverExists frags_220)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_220_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_220 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_220_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_220_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_220_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_220_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_220_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_220_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_220_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(220) = 15`. -/
theorem tau_220_eq : tau frags_220 = 15 := le_antisymm tau_220_le tau_220_ge

end ConcreteTau220

/-! ## Concrete τ for d₀ = 880 -/

section ConcreteTau880

/-- Maximal residual fragments for d₀ = 880. -/
def frags_880 : Finset (Finset (ZMod 880)) :=
  {({2, 27, 52, 77, 102, 127, 152, 177, 202} : Finset (ZMod 880)),
   ({3, 28, 53, 78, 103, 128, 153, 178, 203} : Finset (ZMod 880)),
   ({17, 42, 67, 92, 117, 142, 167, 192, 217} : Finset (ZMod 880)),
   ({18, 43, 68, 93, 118, 143, 168, 193, 218} : Finset (ZMod 880)),
   ({6, 31, 56, 81, 106, 131, 156, 206} : Finset (ZMod 880)),
   ({14, 64, 89, 114, 139, 164, 189, 214} : Finset (ZMod 880)),
   ({11, 36, 61, 86, 111, 136, 186} : Finset (ZMod 880)),
   ({21, 71, 96, 121, 146, 171, 196} : Finset (ZMod 880)),
   ({24, 49, 74, 99, 124, 149, 199} : Finset (ZMod 880)),
   ({34, 84, 109, 134, 159, 184, 209} : Finset (ZMod 880)),
   ({22, 47, 72, 97, 122, 172} : Finset (ZMod 880)),
   ({3, 35, 67, 99, 131, 195} : Finset (ZMod 880)),
   ({48, 98, 123, 148, 173, 198} : Finset (ZMod 880)),
   ({11, 43, 75, 139, 171, 203} : Finset (ZMod 880)),
   ({17, 49, 81, 145, 177, 209} : Finset (ZMod 880)),
   ({25, 89, 121, 153, 185, 217} : Finset (ZMod 880)),
   ({21, 53, 85, 117, 149} : Finset (ZMod 880)),
   ({15, 47, 111, 143, 175} : Finset (ZMod 880)),
   ({71, 103, 135, 167, 199} : Finset (ZMod 880)),
   ({45, 77, 109, 173, 205} : Finset (ZMod 880)),
   ({31, 95, 127, 159} : Finset (ZMod 880)),
   ({61, 93, 125, 189} : Finset (ZMod 880)),
   ({6, 70, 134, 198} : Finset (ZMod 880)),
   ({14, 78, 142, 206} : Finset (ZMod 880)),
   ({22, 86, 150, 214} : Finset (ZMod 880)),
   ({27, 123, 155} : Finset (ZMod 880)),
   ({42, 106, 170} : Finset (ZMod 880)),
   ({50, 114, 178} : Finset (ZMod 880)),
   ({65, 97, 193} : Finset (ZMod 880)),
   ({10, 74, 202} : Finset (ZMod 880)),
   ({18, 146, 210} : Finset (ZMod 880)),
   ({34, 98} : Finset (ZMod 880)),
   ({2, 123} : Finset (ZMod 880)),
   ({3, 124} : Finset (ZMod 880)),
   ({6, 127} : Finset (ZMod 880)),
   ({2, 130} : Finset (ZMod 880)),
   ({10, 131} : Finset (ZMod 880)),
   ({14, 135} : Finset (ZMod 880)),
   ({15, 136} : Finset (ZMod 880)),
   ({18, 139} : Finset (ZMod 880)),
   ({21, 142} : Finset (ZMod 880)),
   ({24, 145} : Finset (ZMod 880)),
   ({25, 146} : Finset (ZMod 880)),
   ({27, 148} : Finset (ZMod 880)),
   ({28, 149} : Finset (ZMod 880)),
   ({31, 152} : Finset (ZMod 880)),
   ({34, 155} : Finset (ZMod 880)),
   ({35, 156} : Finset (ZMod 880)),
   ({43, 164} : Finset (ZMod 880)),
   ({47, 168} : Finset (ZMod 880)),
   ({49, 170} : Finset (ZMod 880)),
   ({50, 171} : Finset (ZMod 880)),
   ({52, 173} : Finset (ZMod 880)),
   ({56, 177} : Finset (ZMod 880)),
   ({64, 185} : Finset (ZMod 880)),
   ({65, 186} : Finset (ZMod 880)),
   ({122, 186} : Finset (ZMod 880)),
   ({68, 189} : Finset (ZMod 880)),
   ({71, 192} : Finset (ZMod 880)),
   ({72, 193} : Finset (ZMod 880)),
   ({74, 195} : Finset (ZMod 880)),
   ({75, 196} : Finset (ZMod 880)),
   ({78, 199} : Finset (ZMod 880)),
   ({81, 202} : Finset (ZMod 880)),
   ({84, 205} : Finset (ZMod 880)),
   ({85, 206} : Finset (ZMod 880)),
   ({89, 210} : Finset (ZMod 880)),
   ({93, 214} : Finset (ZMod 880)),
   ({96, 217} : Finset (ZMod 880)),
   ({90, 218} : Finset (ZMod 880)),
   ({97, 218} : Finset (ZMod 880)),
   ({30} : Finset (ZMod 880)),
   ({190} : Finset (ZMod 880))}

/-- Optimal 34-fragment cover of frags_880. -/
def cover_880 : Finset (Finset (ZMod 880)) :=
  {({2, 27, 52, 77, 102, 127, 152, 177, 202} : Finset (ZMod 880)),
   ({3, 28, 53, 78, 103, 128, 153, 178, 203} : Finset (ZMod 880)),
   ({17, 42, 67, 92, 117, 142, 167, 192, 217} : Finset (ZMod 880)),
   ({18, 43, 68, 93, 118, 143, 168, 193, 218} : Finset (ZMod 880)),
   ({6, 31, 56, 81, 106, 131, 156, 206} : Finset (ZMod 880)),
   ({14, 64, 89, 114, 139, 164, 189, 214} : Finset (ZMod 880)),
   ({11, 36, 61, 86, 111, 136, 186} : Finset (ZMod 880)),
   ({21, 71, 96, 121, 146, 171, 196} : Finset (ZMod 880)),
   ({24, 49, 74, 99, 124, 149, 199} : Finset (ZMod 880)),
   ({34, 84, 109, 134, 159, 184, 209} : Finset (ZMod 880)),
   ({22, 47, 72, 97, 122, 172} : Finset (ZMod 880)),
   ({3, 35, 67, 99, 131, 195} : Finset (ZMod 880)),
   ({48, 98, 123, 148, 173, 198} : Finset (ZMod 880)),
   ({11, 43, 75, 139, 171, 203} : Finset (ZMod 880)),
   ({25, 89, 121, 153, 185, 217} : Finset (ZMod 880)),
   ({21, 53, 85, 117, 149} : Finset (ZMod 880)),
   ({15, 47, 111, 143, 175} : Finset (ZMod 880)),
   ({45, 77, 109, 173, 205} : Finset (ZMod 880)),
   ({31, 95, 127, 159} : Finset (ZMod 880)),
   ({61, 93, 125, 189} : Finset (ZMod 880)),
   ({6, 70, 134, 198} : Finset (ZMod 880)),
   ({22, 86, 150, 214} : Finset (ZMod 880)),
   ({27, 123, 155} : Finset (ZMod 880)),
   ({50, 114, 178} : Finset (ZMod 880)),
   ({65, 97, 193} : Finset (ZMod 880)),
   ({10, 74, 202} : Finset (ZMod 880)),
   ({2, 130} : Finset (ZMod 880)),
   ({14, 135} : Finset (ZMod 880)),
   ({24, 145} : Finset (ZMod 880)),
   ({49, 170} : Finset (ZMod 880)),
   ({89, 210} : Finset (ZMod 880)),
   ({90, 218} : Finset (ZMod 880)),
   ({30} : Finset (ZMod 880)),
   ({190} : Finset (ZMod 880))}

set_option maxRecDepth 5000 in
theorem cover_880_card : cover_880.card = 34 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 800000 in
theorem cover_880_is_cover : IsCoverOf frags_880 cover_880 :=
  ⟨by decide, by decide⟩

/-- `τ(880) ≤ 34` -/
theorem tau_880_le : tau frags_880 ≤ 34 :=
  calc tau frags_880 ≤ cover_880.card :=
          Nat.sInf_le ⟨cover_880, cover_880_is_cover, rfl⟩
       _ = 34 := cover_880_card

/-- Matching certificate: 34 atoms, no two in the same fragment of frags_880. -/
def cert_atoms_880 : Finset (ZMod 880) :=
  {10, 25, 30, 35, 36, 45, 48, 50, 56, 64, 65, 70, 75, 85, 90, 92, 95, 96, 102, 118, 124, 125, 128, 130, 135, 145, 150, 155, 170, 172, 175, 184, 190, 210}

set_option maxRecDepth 20000 in
theorem cert_atoms_880_card : cert_atoms_880.card = 34 := by decide

set_option maxRecDepth 20000 in
theorem cert_880_in_frags : cert_atoms_880 ⊆ frags_880.biUnion id := by decide

set_option maxRecDepth 20000 in
theorem cert_880_matching : ∀ f ∈ frags_880, (cert_atoms_880 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 20000 in
/-- `34 ≤ τ(880)`: matching certificate lower bound. -/
theorem tau_880_ge : 34 ≤ tau frags_880 := by
  unfold tau
  apply le_csInf (minCoverExists frags_880)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_880_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_880 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_880_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_880_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_880_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_880_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_880_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_880_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_880_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(880) = 34`. -/
theorem tau_880_eq : tau frags_880 = 34 := le_antisymm tau_880_le tau_880_ge

end ConcreteTau880

/-! ## Concrete τ for d₀ = 1760 -/

section ConcreteTau1760

/-- Maximal residual fragments for d₀ = 1760. -/
def frags_1760 : Finset (Finset (ZMod 1760)) :=
  {({3, 28, 53, 78, 103, 128, 153, 178, 203} : Finset (ZMod 1760)),
   ({17, 42, 67, 92, 117, 142, 167, 192, 217} : Finset (ZMod 1760)),
   ({21, 46, 71, 96, 121, 146, 171, 196} : Finset (ZMod 1760)),
   ({22, 47, 72, 97, 122, 147, 172, 197} : Finset (ZMod 1760)),
   ({23, 48, 73, 98, 123, 148, 173, 198} : Finset (ZMod 1760)),
   ({24, 49, 74, 99, 124, 149, 174, 199} : Finset (ZMod 1760)),
   ({9, 34, 84, 109, 134, 159, 184, 209} : Finset (ZMod 1760)),
   ({11, 36, 61, 86, 111, 136, 186, 211} : Finset (ZMod 1760)),
   ({21, 85, 149} : Finset (ZMod 1760)),
   ({45, 109, 173} : Finset (ZMod 1760)),
   ({47, 111, 175} : Finset (ZMod 1760)),
   ({3, 67, 195} : Finset (ZMod 1760)),
   ({71, 135, 199} : Finset (ZMod 1760)),
   ({11, 75, 203} : Finset (ZMod 1760)),
   ({17, 145, 209} : Finset (ZMod 1760)),
   ({25, 153, 217} : Finset (ZMod 1760)),
   ({9, 73} : Finset (ZMod 1760)),
   ({35, 99} : Finset (ZMod 1760)),
   ({53, 117} : Finset (ZMod 1760)),
   ({3, 124} : Finset (ZMod 1760)),
   ({61, 125} : Finset (ZMod 1760)),
   ({9, 130} : Finset (ZMod 1760)),
   ({15, 136} : Finset (ZMod 1760)),
   ({21, 142} : Finset (ZMod 1760)),
   ({24, 145} : Finset (ZMod 1760)),
   ({25, 146} : Finset (ZMod 1760)),
   ({28, 149} : Finset (ZMod 1760)),
   ({22, 150} : Finset (ZMod 1760)),
   ({34, 155} : Finset (ZMod 1760)),
   ({95, 159} : Finset (ZMod 1760)),
   ({46, 167} : Finset (ZMod 1760)),
   ({103, 167} : Finset (ZMod 1760)),
   ({42, 170} : Finset (ZMod 1760)),
   ({49, 170} : Finset (ZMod 1760)),
   ({50, 171} : Finset (ZMod 1760)),
   ({46, 174} : Finset (ZMod 1760)),
   ({53, 174} : Finset (ZMod 1760)),
   ({50, 178} : Finset (ZMod 1760)),
   ({121, 185} : Finset (ZMod 1760)),
   ({65, 186} : Finset (ZMod 1760)),
   ({71, 192} : Finset (ZMod 1760)),
   ({74, 195} : Finset (ZMod 1760)),
   ({75, 196} : Finset (ZMod 1760)),
   ({5, 197} : Finset (ZMod 1760)),
   ({70, 198} : Finset (ZMod 1760)),
   ({78, 199} : Finset (ZMod 1760)),
   ({84, 205} : Finset (ZMod 1760)),
   ({90, 211} : Finset (ZMod 1760)),
   ({147, 211} : Finset (ZMod 1760)),
   ({23, 215} : Finset (ZMod 1760)),
   ({96, 217} : Finset (ZMod 1760)),
   ({10} : Finset (ZMod 1760)),
   ({30} : Finset (ZMod 1760)),
   ({190} : Finset (ZMod 1760)),
   ({210} : Finset (ZMod 1760))}

/-- Optimal 36-fragment cover of frags_1760. -/
def cover_1760 : Finset (Finset (ZMod 1760)) :=
  {({3, 28, 53, 78, 103, 128, 153, 178, 203} : Finset (ZMod 1760)),
   ({17, 42, 67, 92, 117, 142, 167, 192, 217} : Finset (ZMod 1760)),
   ({21, 46, 71, 96, 121, 146, 171, 196} : Finset (ZMod 1760)),
   ({22, 47, 72, 97, 122, 147, 172, 197} : Finset (ZMod 1760)),
   ({23, 48, 73, 98, 123, 148, 173, 198} : Finset (ZMod 1760)),
   ({24, 49, 74, 99, 124, 149, 174, 199} : Finset (ZMod 1760)),
   ({9, 34, 84, 109, 134, 159, 184, 209} : Finset (ZMod 1760)),
   ({11, 36, 61, 86, 111, 136, 186, 211} : Finset (ZMod 1760)),
   ({21, 85, 149} : Finset (ZMod 1760)),
   ({45, 109, 173} : Finset (ZMod 1760)),
   ({47, 111, 175} : Finset (ZMod 1760)),
   ({71, 135, 199} : Finset (ZMod 1760)),
   ({11, 75, 203} : Finset (ZMod 1760)),
   ({25, 153, 217} : Finset (ZMod 1760)),
   ({35, 99} : Finset (ZMod 1760)),
   ({61, 125} : Finset (ZMod 1760)),
   ({9, 130} : Finset (ZMod 1760)),
   ({15, 136} : Finset (ZMod 1760)),
   ({24, 145} : Finset (ZMod 1760)),
   ({22, 150} : Finset (ZMod 1760)),
   ({34, 155} : Finset (ZMod 1760)),
   ({95, 159} : Finset (ZMod 1760)),
   ({49, 170} : Finset (ZMod 1760)),
   ({50, 171} : Finset (ZMod 1760)),
   ({121, 185} : Finset (ZMod 1760)),
   ({65, 186} : Finset (ZMod 1760)),
   ({74, 195} : Finset (ZMod 1760)),
   ({5, 197} : Finset (ZMod 1760)),
   ({70, 198} : Finset (ZMod 1760)),
   ({84, 205} : Finset (ZMod 1760)),
   ({90, 211} : Finset (ZMod 1760)),
   ({23, 215} : Finset (ZMod 1760)),
   ({10} : Finset (ZMod 1760)),
   ({30} : Finset (ZMod 1760)),
   ({190} : Finset (ZMod 1760)),
   ({210} : Finset (ZMod 1760))}

set_option maxRecDepth 5000 in
theorem cover_1760_card : cover_1760.card = 36 := by decide
set_option maxRecDepth 5000 in
set_option maxHeartbeats 800000 in
theorem cover_1760_is_cover : IsCoverOf frags_1760 cover_1760 :=
  ⟨by decide, by decide⟩

/-- `τ(1760) ≤ 36` -/
theorem tau_1760_le : tau frags_1760 ≤ 36 :=
  calc tau frags_1760 ≤ cover_1760.card :=
          Nat.sInf_le ⟨cover_1760, cover_1760_is_cover, rfl⟩
       _ = 36 := cover_1760_card

/-- Matching certificate: 36 atoms, no two in the same fragment of frags_1760. -/
def cert_atoms_1760 : Finset (ZMod 1760) :=
  {5, 10, 15, 25, 30, 35, 36, 45, 48, 50, 65, 70, 72, 75, 85, 90, 92, 95, 96, 124, 125, 128, 130, 134, 135, 145, 150, 155, 170, 175, 185, 190, 195, 205, 210, 215}

set_option maxRecDepth 20000 in
theorem cert_atoms_1760_card : cert_atoms_1760.card = 36 := by decide

set_option maxRecDepth 20000 in
theorem cert_1760_in_frags : cert_atoms_1760 ⊆ frags_1760.biUnion id := by decide

set_option maxRecDepth 20000 in
theorem cert_1760_matching : ∀ f ∈ frags_1760, (cert_atoms_1760 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 20000 in
/-- `36 ≤ τ(1760)`: matching certificate lower bound. -/
theorem tau_1760_ge : 36 ≤ tau frags_1760 := by
  unfold tau
  apply le_csInf (minCoverExists frags_1760)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_1760_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_1760 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_1760_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_1760_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_1760_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_1760_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_1760_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_1760_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_1760_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(1760) = 36`. -/
theorem tau_1760_eq : tau frags_1760 = 36 := le_antisymm tau_1760_le tau_1760_ge

end ConcreteTau1760

/-! ## Concrete τ for d₀ = 4400 -/

section ConcreteTau4400

/-- Maximal residual fragments for d₀ = 4400. -/
def frags_4400 : Finset (Finset (ZMod 4400)) :=
  {({29, 61, 93, 125, 157, 189} : Finset (ZMod 4400)),
   ({31, 63, 95, 127, 159, 191} : Finset (ZMod 4400)),
   ({1, 33, 65, 97, 129, 193} : Finset (ZMod 4400)),
   ({27, 91, 123, 155, 187, 219} : Finset (ZMod 4400)),
   ({2, 66, 130, 194} : Finset (ZMod 4400)),
   ({6, 70, 134, 198} : Finset (ZMod 4400)),
   ({10, 74, 138, 202} : Finset (ZMod 4400)),
   ({14, 78, 142, 206} : Finset (ZMod 4400)),
   ({18, 82, 146, 210} : Finset (ZMod 4400)),
   ({22, 86, 150, 214} : Finset (ZMod 4400)),
   ({26, 90, 154, 218} : Finset (ZMod 4400)),
   ({30, 94, 158} : Finset (ZMod 4400)),
   ({34, 98, 162} : Finset (ZMod 4400)),
   ({58, 122, 186} : Finset (ZMod 4400)),
   ({62, 126, 190} : Finset (ZMod 4400)),
   ({1, 122} : Finset (ZMod 4400)),
   ({2, 123} : Finset (ZMod 4400)),
   ({4, 125} : Finset (ZMod 4400)),
   ({1, 126} : Finset (ZMod 4400)),
   ({2, 127} : Finset (ZMod 4400)),
   ({6, 127} : Finset (ZMod 4400)),
   ({4, 129} : Finset (ZMod 4400)),
   ({8, 129} : Finset (ZMod 4400)),
   ({27, 148} : Finset (ZMod 4400)),
   ({29, 150} : Finset (ZMod 4400)),
   ({27, 152} : Finset (ZMod 4400)),
   ({31, 152} : Finset (ZMod 4400)),
   ({29, 154} : Finset (ZMod 4400)),
   ({34, 155} : Finset (ZMod 4400)),
   ({31, 156} : Finset (ZMod 4400)),
   ({32, 157} : Finset (ZMod 4400)),
   ({36, 157} : Finset (ZMod 4400)),
   ({33, 158} : Finset (ZMod 4400)),
   ({34, 159} : Finset (ZMod 4400)),
   ({63, 184} : Finset (ZMod 4400)),
   ({61, 186} : Finset (ZMod 4400)),
   ({65, 186} : Finset (ZMod 4400)),
   ({62, 187} : Finset (ZMod 4400)),
   ({63, 188} : Finset (ZMod 4400)),
   ({64, 189} : Finset (ZMod 4400)),
   ({68, 189} : Finset (ZMod 4400)),
   ({66, 191} : Finset (ZMod 4400)),
   ({70, 191} : Finset (ZMod 4400)),
   ({68, 193} : Finset (ZMod 4400)),
   ({72, 193} : Finset (ZMod 4400)),
   ({91, 212} : Finset (ZMod 4400)),
   ({93, 214} : Finset (ZMod 4400)),
   ({91, 216} : Finset (ZMod 4400)),
   ({95, 216} : Finset (ZMod 4400)),
   ({93, 218} : Finset (ZMod 4400)),
   ({97, 218} : Finset (ZMod 4400)),
   ({94, 219} : Finset (ZMod 4400)),
   ({98, 219} : Finset (ZMod 4400)),
   ({12} : Finset (ZMod 4400)),
   ({16} : Finset (ZMod 4400)),
   ({24} : Finset (ZMod 4400)),
   ({28} : Finset (ZMod 4400)),
   ({48} : Finset (ZMod 4400)),
   ({52} : Finset (ZMod 4400)),
   ({56} : Finset (ZMod 4400)),
   ({76} : Finset (ZMod 4400)),
   ({84} : Finset (ZMod 4400)),
   ({92} : Finset (ZMod 4400)),
   ({128} : Finset (ZMod 4400)),
   ({136} : Finset (ZMod 4400)),
   ({144} : Finset (ZMod 4400)),
   ({164} : Finset (ZMod 4400)),
   ({168} : Finset (ZMod 4400)),
   ({172} : Finset (ZMod 4400)),
   ({192} : Finset (ZMod 4400)),
   ({196} : Finset (ZMod 4400)),
   ({204} : Finset (ZMod 4400)),
   ({208} : Finset (ZMod 4400))}

/-- Optimal 49-fragment cover of frags_4400. -/
def cover_4400 : Finset (Finset (ZMod 4400)) :=
  {({29, 61, 93, 125, 157, 189} : Finset (ZMod 4400)),
   ({31, 63, 95, 127, 159, 191} : Finset (ZMod 4400)),
   ({1, 33, 65, 97, 129, 193} : Finset (ZMod 4400)),
   ({27, 91, 123, 155, 187, 219} : Finset (ZMod 4400)),
   ({2, 66, 130, 194} : Finset (ZMod 4400)),
   ({6, 70, 134, 198} : Finset (ZMod 4400)),
   ({10, 74, 138, 202} : Finset (ZMod 4400)),
   ({14, 78, 142, 206} : Finset (ZMod 4400)),
   ({18, 82, 146, 210} : Finset (ZMod 4400)),
   ({22, 86, 150, 214} : Finset (ZMod 4400)),
   ({26, 90, 154, 218} : Finset (ZMod 4400)),
   ({30, 94, 158} : Finset (ZMod 4400)),
   ({34, 98, 162} : Finset (ZMod 4400)),
   ({58, 122, 186} : Finset (ZMod 4400)),
   ({62, 126, 190} : Finset (ZMod 4400)),
   ({4, 125} : Finset (ZMod 4400)),
   ({8, 129} : Finset (ZMod 4400)),
   ({27, 148} : Finset (ZMod 4400)),
   ({27, 152} : Finset (ZMod 4400)),
   ({31, 156} : Finset (ZMod 4400)),
   ({32, 157} : Finset (ZMod 4400)),
   ({36, 157} : Finset (ZMod 4400)),
   ({63, 184} : Finset (ZMod 4400)),
   ({63, 188} : Finset (ZMod 4400)),
   ({64, 189} : Finset (ZMod 4400)),
   ({68, 189} : Finset (ZMod 4400)),
   ({72, 193} : Finset (ZMod 4400)),
   ({91, 212} : Finset (ZMod 4400)),
   ({95, 216} : Finset (ZMod 4400)),
   ({12} : Finset (ZMod 4400)),
   ({16} : Finset (ZMod 4400)),
   ({24} : Finset (ZMod 4400)),
   ({28} : Finset (ZMod 4400)),
   ({48} : Finset (ZMod 4400)),
   ({52} : Finset (ZMod 4400)),
   ({56} : Finset (ZMod 4400)),
   ({76} : Finset (ZMod 4400)),
   ({84} : Finset (ZMod 4400)),
   ({92} : Finset (ZMod 4400)),
   ({128} : Finset (ZMod 4400)),
   ({136} : Finset (ZMod 4400)),
   ({144} : Finset (ZMod 4400)),
   ({164} : Finset (ZMod 4400)),
   ({168} : Finset (ZMod 4400)),
   ({172} : Finset (ZMod 4400)),
   ({192} : Finset (ZMod 4400)),
   ({196} : Finset (ZMod 4400)),
   ({204} : Finset (ZMod 4400)),
   ({208} : Finset (ZMod 4400))}

set_option maxRecDepth 10000 in
theorem cover_4400_card : cover_4400.card = 49 := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem cover_4400_is_cover : IsCoverOf frags_4400 cover_4400 :=
  ⟨by decide, by decide⟩

/-- `τ(4400) ≤ 49` -/
theorem tau_4400_le : tau frags_4400 ≤ 49 :=
  calc tau frags_4400 ≤ cover_4400.card :=
          Nat.sInf_le ⟨cover_4400, cover_4400_is_cover, rfl⟩
       _ = 49 := cover_4400_card

/-- Matching certificate: 49 atoms, no two in the same fragment of frags_4400. -/
def cert_atoms_4400 : Finset (ZMod 4400) :=
  {4, 8, 10, 12, 14, 16, 18, 22, 24, 26, 28, 30, 32, 33, 36, 48, 52, 56, 58, 61, 64, 68, 72, 76, 84, 92, 123, 128, 130, 134, 136, 144, 148, 152, 156, 159, 162, 164, 168, 172, 184, 188, 190, 192, 196, 204, 208, 212, 216}

set_option maxRecDepth 20000 in
theorem cert_atoms_4400_card : cert_atoms_4400.card = 49 := by decide

set_option maxRecDepth 20000 in
theorem cert_4400_in_frags : cert_atoms_4400 ⊆ frags_4400.biUnion id := by decide

set_option maxRecDepth 20000 in
theorem cert_4400_matching : ∀ f ∈ frags_4400, (cert_atoms_4400 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 20000 in
/-- `49 ≤ τ(4400)`: matching certificate lower bound. -/
theorem tau_4400_ge : 49 ≤ tau frags_4400 := by
  unfold tau
  apply le_csInf (minCoverExists frags_4400)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_4400_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_4400 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_4400_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_4400_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_4400_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_4400_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_4400_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_4400_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_4400_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(4400) = 49`. -/
theorem tau_4400_eq : tau frags_4400 = 49 := le_antisymm tau_4400_le tau_4400_ge

end ConcreteTau4400

/-! ## Concrete τ for d₀ = 8800 -/

section ConcreteTau8800

/-- Maximal residual fragments for d₀ = 8800. -/
def frags_8800 : Finset (Finset (ZMod 8800)) :=
  {({5, 69, 133, 197} : Finset (ZMod 8800)),
   ({11, 75, 139, 203} : Finset (ZMod 8800)),
   ({17, 81, 145, 209} : Finset (ZMod 8800)),
   ({23, 87, 151, 215} : Finset (ZMod 8800)),
   ({9, 73, 137} : Finset (ZMod 8800)),
   ({21, 85, 149} : Finset (ZMod 8800)),
   ({25, 89, 153} : Finset (ZMod 8800)),
   ({27, 91, 155} : Finset (ZMod 8800)),
   ({29, 93, 157} : Finset (ZMod 8800)),
   ({31, 95, 159} : Finset (ZMod 8800)),
   ({61, 125, 189} : Finset (ZMod 8800)),
   ({63, 127, 191} : Finset (ZMod 8800)),
   ({65, 129, 193} : Finset (ZMod 8800)),
   ({67, 131, 195} : Finset (ZMod 8800)),
   ({71, 135, 199} : Finset (ZMod 8800)),
   ({13, 77, 205} : Finset (ZMod 8800)),
   ({15, 143, 207} : Finset (ZMod 8800)),
   ({83, 147, 211} : Finset (ZMod 8800)),
   ({33, 97} : Finset (ZMod 8800)),
   ({2, 123} : Finset (ZMod 8800)),
   ({4, 125} : Finset (ZMod 8800)),
   ({5, 126} : Finset (ZMod 8800)),
   ({2, 127} : Finset (ZMod 8800)),
   ({6, 127} : Finset (ZMod 8800)),
   ({4, 129} : Finset (ZMod 8800)),
   ({8, 129} : Finset (ZMod 8800)),
   ({2, 130} : Finset (ZMod 8800)),
   ({9, 130} : Finset (ZMod 8800)),
   ({6, 131} : Finset (ZMod 8800)),
   ({10, 131} : Finset (ZMod 8800)),
   ({8, 133} : Finset (ZMod 8800)),
   ({12, 133} : Finset (ZMod 8800)),
   ({6, 134} : Finset (ZMod 8800)),
   ({9, 134} : Finset (ZMod 8800)),
   ({13, 134} : Finset (ZMod 8800)),
   ({14, 135} : Finset (ZMod 8800)),
   ({11, 136} : Finset (ZMod 8800)),
   ({15, 136} : Finset (ZMod 8800)),
   ({12, 137} : Finset (ZMod 8800)),
   ({16, 137} : Finset (ZMod 8800)),
   ({10, 138} : Finset (ZMod 8800)),
   ({13, 138} : Finset (ZMod 8800)),
   ({17, 138} : Finset (ZMod 8800)),
   ({14, 139} : Finset (ZMod 8800)),
   ({18, 139} : Finset (ZMod 8800)),
   ({14, 142} : Finset (ZMod 8800)),
   ({17, 142} : Finset (ZMod 8800)),
   ({21, 142} : Finset (ZMod 8800)),
   ({18, 143} : Finset (ZMod 8800)),
   ({23, 144} : Finset (ZMod 8800)),
   ({24, 145} : Finset (ZMod 8800)),
   ({18, 146} : Finset (ZMod 8800)),
   ({21, 146} : Finset (ZMod 8800)),
   ({25, 146} : Finset (ZMod 8800)),
   ({22, 147} : Finset (ZMod 8800)),
   ({26, 147} : Finset (ZMod 8800)),
   ({23, 148} : Finset (ZMod 8800)),
   ({27, 148} : Finset (ZMod 8800)),
   ({24, 149} : Finset (ZMod 8800)),
   ({28, 149} : Finset (ZMod 8800)),
   ({22, 150} : Finset (ZMod 8800)),
   ({29, 150} : Finset (ZMod 8800)),
   ({26, 151} : Finset (ZMod 8800)),
   ({30, 151} : Finset (ZMod 8800)),
   ({27, 152} : Finset (ZMod 8800)),
   ({31, 152} : Finset (ZMod 8800)),
   ({28, 153} : Finset (ZMod 8800)),
   ({32, 153} : Finset (ZMod 8800)),
   ({26, 154} : Finset (ZMod 8800)),
   ({29, 154} : Finset (ZMod 8800)),
   ({34, 155} : Finset (ZMod 8800)),
   ({31, 156} : Finset (ZMod 8800)),
   ({32, 157} : Finset (ZMod 8800)),
   ({36, 157} : Finset (ZMod 8800)),
   ({30, 158} : Finset (ZMod 8800)),
   ({33, 158} : Finset (ZMod 8800)),
   ({34, 159} : Finset (ZMod 8800)),
   ({38, 159} : Finset (ZMod 8800)),
   ({34, 162} : Finset (ZMod 8800)),
   ({38, 166} : Finset (ZMod 8800)),
   ({42, 170} : Finset (ZMod 8800)),
   ({46, 174} : Finset (ZMod 8800)),
   ({50, 178} : Finset (ZMod 8800)),
   ({54, 182} : Finset (ZMod 8800)),
   ({61, 182} : Finset (ZMod 8800)),
   ({63, 184} : Finset (ZMod 8800)),
   ({58, 186} : Finset (ZMod 8800)),
   ({61, 186} : Finset (ZMod 8800)),
   ({65, 186} : Finset (ZMod 8800)),
   ({62, 187} : Finset (ZMod 8800)),
   ({123, 187} : Finset (ZMod 8800)),
   ({63, 188} : Finset (ZMod 8800)),
   ({67, 188} : Finset (ZMod 8800)),
   ({64, 189} : Finset (ZMod 8800)),
   ({68, 189} : Finset (ZMod 8800)),
   ({62, 190} : Finset (ZMod 8800)),
   ({69, 190} : Finset (ZMod 8800)),
   ({66, 191} : Finset (ZMod 8800)),
   ({70, 191} : Finset (ZMod 8800)),
   ({67, 192} : Finset (ZMod 8800)),
   ({71, 192} : Finset (ZMod 8800)),
   ({68, 193} : Finset (ZMod 8800)),
   ({72, 193} : Finset (ZMod 8800)),
   ({66, 194} : Finset (ZMod 8800)),
   ({69, 194} : Finset (ZMod 8800)),
   ({73, 194} : Finset (ZMod 8800)),
   ({74, 195} : Finset (ZMod 8800)),
   ({71, 196} : Finset (ZMod 8800)),
   ({75, 196} : Finset (ZMod 8800)),
   ({72, 197} : Finset (ZMod 8800)),
   ({76, 197} : Finset (ZMod 8800)),
   ({70, 198} : Finset (ZMod 8800)),
   ({73, 198} : Finset (ZMod 8800)),
   ({74, 199} : Finset (ZMod 8800)),
   ({78, 199} : Finset (ZMod 8800)),
   ({74, 202} : Finset (ZMod 8800)),
   ({77, 202} : Finset (ZMod 8800)),
   ({81, 202} : Finset (ZMod 8800)),
   ({78, 203} : Finset (ZMod 8800)),
   ({82, 203} : Finset (ZMod 8800)),
   ({83, 204} : Finset (ZMod 8800)),
   ({84, 205} : Finset (ZMod 8800)),
   ({78, 206} : Finset (ZMod 8800)),
   ({81, 206} : Finset (ZMod 8800)),
   ({85, 206} : Finset (ZMod 8800)),
   ({82, 207} : Finset (ZMod 8800)),
   ({86, 207} : Finset (ZMod 8800)),
   ({83, 208} : Finset (ZMod 8800)),
   ({87, 208} : Finset (ZMod 8800)),
   ({84, 209} : Finset (ZMod 8800)),
   ({82, 210} : Finset (ZMod 8800)),
   ({89, 210} : Finset (ZMod 8800)),
   ({86, 211} : Finset (ZMod 8800)),
   ({90, 211} : Finset (ZMod 8800)),
   ({87, 212} : Finset (ZMod 8800)),
   ({91, 212} : Finset (ZMod 8800)),
   ({86, 214} : Finset (ZMod 8800)),
   ({89, 214} : Finset (ZMod 8800)),
   ({93, 214} : Finset (ZMod 8800)),
   ({94, 215} : Finset (ZMod 8800)),
   ({91, 216} : Finset (ZMod 8800)),
   ({95, 216} : Finset (ZMod 8800)),
   ({90, 218} : Finset (ZMod 8800)),
   ({93, 218} : Finset (ZMod 8800)),
   ({97, 218} : Finset (ZMod 8800)),
   ({48} : Finset (ZMod 8800)),
   ({52} : Finset (ZMod 8800)),
   ({56} : Finset (ZMod 8800)),
   ({92} : Finset (ZMod 8800)),
   ({128} : Finset (ZMod 8800)),
   ({164} : Finset (ZMod 8800)),
   ({168} : Finset (ZMod 8800)),
   ({172} : Finset (ZMod 8800))}

/-- Optimal 79-fragment cover of frags_8800. -/
def cover_8800 : Finset (Finset (ZMod 8800)) :=
  {({17, 81, 145, 209} : Finset (ZMod 8800)),
   ({23, 87, 151, 215} : Finset (ZMod 8800)),
   ({25, 89, 153} : Finset (ZMod 8800)),
   ({27, 91, 155} : Finset (ZMod 8800)),
   ({29, 93, 157} : Finset (ZMod 8800)),
   ({31, 95, 159} : Finset (ZMod 8800)),
   ({65, 129, 193} : Finset (ZMod 8800)),
   ({71, 135, 199} : Finset (ZMod 8800)),
   ({15, 143, 207} : Finset (ZMod 8800)),
   ({83, 147, 211} : Finset (ZMod 8800)),
   ({33, 97} : Finset (ZMod 8800)),
   ({2, 123} : Finset (ZMod 8800)),
   ({4, 125} : Finset (ZMod 8800)),
   ({5, 126} : Finset (ZMod 8800)),
   ({6, 127} : Finset (ZMod 8800)),
   ({8, 129} : Finset (ZMod 8800)),
   ({9, 130} : Finset (ZMod 8800)),
   ({10, 131} : Finset (ZMod 8800)),
   ({12, 133} : Finset (ZMod 8800)),
   ({13, 134} : Finset (ZMod 8800)),
   ({11, 136} : Finset (ZMod 8800)),
   ({16, 137} : Finset (ZMod 8800)),
   ({17, 138} : Finset (ZMod 8800)),
   ({18, 139} : Finset (ZMod 8800)),
   ({14, 142} : Finset (ZMod 8800)),
   ({23, 144} : Finset (ZMod 8800)),
   ({24, 145} : Finset (ZMod 8800)),
   ({21, 146} : Finset (ZMod 8800)),
   ({27, 148} : Finset (ZMod 8800)),
   ({28, 149} : Finset (ZMod 8800)),
   ({22, 150} : Finset (ZMod 8800)),
   ({27, 152} : Finset (ZMod 8800)),
   ({32, 153} : Finset (ZMod 8800)),
   ({26, 154} : Finset (ZMod 8800)),
   ({31, 156} : Finset (ZMod 8800)),
   ({36, 157} : Finset (ZMod 8800)),
   ({30, 158} : Finset (ZMod 8800)),
   ({34, 162} : Finset (ZMod 8800)),
   ({38, 166} : Finset (ZMod 8800)),
   ({42, 170} : Finset (ZMod 8800)),
   ({46, 174} : Finset (ZMod 8800)),
   ({50, 178} : Finset (ZMod 8800)),
   ({54, 182} : Finset (ZMod 8800)),
   ({63, 184} : Finset (ZMod 8800)),
   ({58, 186} : Finset (ZMod 8800)),
   ({61, 186} : Finset (ZMod 8800)),
   ({62, 187} : Finset (ZMod 8800)),
   ({67, 188} : Finset (ZMod 8800)),
   ({64, 189} : Finset (ZMod 8800)),
   ({68, 189} : Finset (ZMod 8800)),
   ({69, 190} : Finset (ZMod 8800)),
   ({70, 191} : Finset (ZMod 8800)),
   ({67, 192} : Finset (ZMod 8800)),
   ({72, 193} : Finset (ZMod 8800)),
   ({66, 194} : Finset (ZMod 8800)),
   ({74, 195} : Finset (ZMod 8800)),
   ({75, 196} : Finset (ZMod 8800)),
   ({76, 197} : Finset (ZMod 8800)),
   ({73, 198} : Finset (ZMod 8800)),
   ({77, 202} : Finset (ZMod 8800)),
   ({78, 203} : Finset (ZMod 8800)),
   ({83, 204} : Finset (ZMod 8800)),
   ({84, 205} : Finset (ZMod 8800)),
   ({85, 206} : Finset (ZMod 8800)),
   ({87, 208} : Finset (ZMod 8800)),
   ({82, 210} : Finset (ZMod 8800)),
   ({87, 212} : Finset (ZMod 8800)),
   ({86, 214} : Finset (ZMod 8800)),
   ({94, 215} : Finset (ZMod 8800)),
   ({91, 216} : Finset (ZMod 8800)),
   ({90, 218} : Finset (ZMod 8800)),
   ({48} : Finset (ZMod 8800)),
   ({52} : Finset (ZMod 8800)),
   ({56} : Finset (ZMod 8800)),
   ({92} : Finset (ZMod 8800)),
   ({128} : Finset (ZMod 8800)),
   ({164} : Finset (ZMod 8800)),
   ({168} : Finset (ZMod 8800)),
   ({172} : Finset (ZMod 8800))}

set_option maxRecDepth 10000 in
theorem cover_8800_card : cover_8800.card = 79 := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
theorem cover_8800_is_cover : IsCoverOf frags_8800 cover_8800 :=
  ⟨by decide, by decide⟩

/-- `τ(8800) ≤ 79` -/
theorem tau_8800_le : tau frags_8800 ≤ 79 :=
  calc tau frags_8800 ≤ cover_8800.card :=
          Nat.sInf_le ⟨cover_8800, cover_8800_is_cover, rfl⟩
       _ = 79 := cover_8800_card

/-- Matching certificate: 79 atoms, no two in the same fragment of frags_8800. -/
def cert_atoms_8800 : Finset (ZMod 8800) :=
  {4, 8, 12, 16, 24, 28, 32, 36, 42, 46, 48, 50, 52, 54, 56, 58, 61, 62, 64, 65, 66, 68, 69, 70, 72, 73, 74, 76, 77, 78, 81, 82, 84, 85, 86, 89, 90, 92, 93, 94, 97, 123, 126, 127, 128, 130, 131, 134, 135, 136, 138, 139, 142, 143, 144, 146, 147, 148, 150, 151, 152, 154, 155, 156, 158, 159, 162, 164, 166, 168, 172, 184, 188, 192, 196, 204, 208, 212, 216}

set_option maxRecDepth 50000 in
theorem cert_atoms_8800_card : cert_atoms_8800.card = 79 := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
theorem cert_8800_in_frags : cert_atoms_8800 ⊆ frags_8800.biUnion id := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
theorem cert_8800_matching : ∀ f ∈ frags_8800, (cert_atoms_8800 ∩ f).card ≤ 1 := by
  intro f hf; fin_cases hf <;> decide

set_option maxRecDepth 50000 in
/-- `79 ≤ τ(8800)`: matching certificate lower bound. -/
theorem tau_8800_ge : 79 ≤ tau frags_8800 := by
  unfold tau
  apply le_csInf (minCoverExists frags_8800)
  rintro n ⟨S, ⟨hSsub, hScov⟩, rfl⟩
  rw [← cert_atoms_8800_card, ← Fintype.card_coe, ← Fintype.card_coe S]
  apply Fintype.card_le_of_injective
    (fun a : ↑cert_atoms_8800 =>
      (⟨Classical.choose (Finset.mem_biUnion.mp (hScov (cert_8800_in_frags a.2))),
        (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_8800_in_frags a.2)))).1⟩ : ↑S))
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  simp only [Subtype.mk.injEq] at h
  have ha_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_8800_in_frags ha)))).2
  have hb_in := (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_8800_in_frags hb)))).2
  have hb_in' : b ∈ Classical.choose (Finset.mem_biUnion.mp (hScov (cert_8800_in_frags ha))) :=
    h ▸ hb_in
  have hfrag := hSsub
    (Classical.choose_spec (Finset.mem_biUnion.mp (hScov (cert_8800_in_frags ha)))).1
  exact Subtype.ext (Finset.card_le_one.mp (cert_8800_matching _ hfrag)
    a (Finset.mem_inter.mpr ⟨ha, ha_in⟩)
    b (Finset.mem_inter.mpr ⟨hb, hb_in'⟩))

/-- `τ(8800) = 79`. -/
theorem tau_8800_eq : tau frags_8800 = 79 := le_antisymm tau_8800_le tau_8800_ge

end ConcreteTau8800

end ModularSchur.TauClosure
