import ModularSchur.DeficitGrowthInvariant
import ModularSchur.DeficitGrowthRestrictedAET
import ModularSchur.TwoAxisAnchoredExactTransversal

/-!
# Deficit-growth certificate-shape conjecture

This file encodes the *conclusion disjunction* of the D3 certificate-shape
conjecture as a Lean proposition on the same support shell used by the existing
AET and two-axis bridges.  (It does not encode D3 itself: `DyadicCertificateShape`
below takes an arbitrary `cell`/`P` with no dyadic, PID-failing, or `|P| ≥ 2`
hypothesis, and nothing here quantifies over the family `n = 55 * 2 ^ a`.)

D3 as a universal claim is **REFUTED**: the certified fiber
`n = 880, d₀ = 35200, P = (121, 125, 256)` is dyadic, singleton-atom and
PID-failing, and has max packing 48 < axis cover 50.  Each of the three branches
below provably implies `axis_cover = maxPacking`, so no branch can hold there.
See `docs/proofs/dyadic-aet-failure-n880-2026-06-21.md`.

What survives, and is fully proved in this file, is the *shape ⇒ exactness*
implication for each branch.  That is unaffected by the refutation.
-/

namespace ModularSchur.DeficitGrowth

open Classical
open Finset
open ModularSchur.AnchoredExactTransversal
open ModularSchur.ResidueAxis
open ModularSchur.SameSupportFiber
open ModularSchur.TauClosure
open ModularSchur.TwoAxisAnchoredExactTransversal
open ModularSchur.TwoAxisStructural

universe u v w

variable {α : Type u} {ι : Type v} [DecidableEq α] [Fintype ι]

/-- Whole-axis certificate shape for the dyadic conjecture. -/
def WholeAxisCertificate (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) : Prop := by
  classical
  exact ∃ (X : Finset (AtomClass cell.F)) (coord : ι → AtomClass cell.F → ℕ)
    (h : ι) (C : Finset (Finset (AtomClass cell.F))) (Q : Finset (AtomClass cell.F)),
    WholeAxisCover (coordCliques cell P) X coord h C ∧
    AxisPacking (coordCliques cell P) Q ∧
    Q.card = (pi_h X coord h).card

/-- Two-axis certificate shape for the dyadic conjecture. -/
def TwoAxisCertificateShape (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) : Prop := by
  classical
  exact Nonempty (TwoAxisCertificate (coordCliques cell P))

/-- A two-axis certificate shape gives an AET witness whenever the support is
nonempty. -/
theorem hasAET_of_TwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    {P : Finset ℕ} (hP : P.Nonempty)
    (h : TwoAxisCertificateShape cell P) :
    hasAET cell P := by
  exact hasAET_of_twoAxisCertificate cell hP h

/-- Certificate-shape disjunction: one of the three already formalized proof
routes exists.  This is **not** universal on the dyadic PID-failing family — it
fails at `n = 880, d₀ = 35200, P = (121, 125, 256)`.  It is retained because each
disjunct implies exactness. -/
def DyadicCertificateShape (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)]
    (P : Finset ℕ) : Prop := by
  classical
  exact WholeAxisCertificate cell P ∨
    TwoAxisCertificateShape cell P ∨
    hasCornerClusterCarrierAET cell P

/-- Whole-axis certificate shapes imply exactness. -/
theorem axis_cover_eq_maxPacking_of_WholeAxisCertificate
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : WholeAxisCertificate cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  classical
  rcases h with ⟨X, coord, hAxis, C, Q, hC, hQ, hcard⟩
  exact axis_cover_eq_maxPacking_of_wholeAxis
    (frags := coordCliques cell P) (X := X) (coord := coord)
    (h := hAxis) (C := C) (P := Q) hC hQ hcard

/-- Two-axis certificate shapes imply exactness. -/
theorem axis_cover_eq_maxPacking_of_TwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : TwoAxisCertificateShape cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  classical
  by_cases hP : P.Nonempty
  · exact axis_cover_eq_maxPacking_of_hasAET cell
      (hasAET_of_TwoAxisCertificateShape cell hP h)
  · rcases h with ⟨w⟩
    exact axis_cover_eq_maxPacking_of_certificate w

/-- A concrete two-axis certificate on `coordCliques` inhabits the two-axis
branch of the dyadic certificate-shape conjecture. -/
theorem twoAxisCertificateShape_of_certificate
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (w : TwoAxisCertificate (coordCliques cell P)) :
    TwoAxisCertificateShape cell P := by
  exact ⟨w⟩

/-- Transport a residue-axis two-axis certificate onto the normalized-cell
`coordCliques` surface once the fragment families have been identified. -/
theorem twoAxisCertificateShape_of_frags_eq_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {frags : Finset (Finset (AtomClass cell.F))}
    (hfrags : frags = coordCliques cell P)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    TwoAxisCertificateShape cell P := by
  exact certificate_nonempty_of_eq hfrags hw

/-- Transport a two-axis certificate from an injective point carrier onto the
normalized-cell `coordCliques` surface once the generated image has been
identified with the scanner-facing fragment family. -/
theorem twoAxisCertificateShape_of_imageFrags_eq_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hfrags : imageFrags φ frags = coordCliques cell P)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    TwoAxisCertificateShape cell P := by
  exact twoAxisCertificateShape_of_frags_eq_coordCliques cell P hfrags
    (certificate_nonempty_image hφ hw)

/-- Transport an injective point-carrier two-axis certificate onto
`coordCliques` when the generated image family is a subfamily of
`coordCliques` and every coordinate clique is dominated by one generated image
fragment. This is the scanner-facing form used by reduced residue-axis rows. -/
theorem twoAxisCertificateShape_of_imageFrags_subset_dominated_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hsub : imageFrags φ frags ⊆ coordCliques cell P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ imageFrags φ frags, C ⊆ F)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    TwoAxisCertificateShape cell P := by
  exact certificate_nonempty_of_subset_dominated hsub hdom
    (certificate_nonempty_image hφ hw)

/-- Source-level fragment image membership is the same as the `imageFrags`
subfamily hypothesis used by dominated two-axis transport. This keeps generated
row files from having to unfold `imageFrags` themselves. -/
theorem imageFrags_subset_coordCliques_of_forall_image_mem
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hmem : ∀ F ∈ frags, F.image φ ∈ coordCliques cell P) :
    imageFrags φ frags ⊆ coordCliques cell P := by
  intro F hF
  unfold imageFrags at hF
  rcases Finset.mem_image.mp hF with ⟨raw, hraw, rfl⟩
  exact hmem raw hraw

/-- Source-level domination by an image of a raw carrier fragment is the same as
domination by the generated `imageFrags` family. -/
theorem coordCliques_dominated_by_imageFrags_of_forall_image_dominated
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ frags, C ⊆ F.image φ) :
    ∀ C ∈ coordCliques cell P, ∃ F ∈ imageFrags φ frags, C ⊆ F := by
  intro C hC
  rcases hdom C hC with ⟨raw, hraw, hsub⟩
  exact ⟨raw.image φ, Finset.mem_image.mpr ⟨raw, hraw, rfl⟩, hsub⟩

/-- Injective equality of images forces equality of the original finite
carrier subsets. -/
theorem finset_eq_of_image_eq_image_of_injective
    {γ : Type w} [DecidableEq γ]
    {δ : Type*} [DecidableEq δ]
    {φ : γ → δ} (hφ : Function.Injective φ)
    {S T : Finset γ}
    (hST : S.image φ = T.image φ) :
    S = T := by
  apply Finset.Subset.antisymm
  · intro s hs
    have hs' : φ s ∈ T.image φ := by
      rw [← hST]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    rcases Finset.mem_image.mp hs' with ⟨t, ht, hEq⟩
    have hts : t = s := hφ hEq
    simpa [hts] using ht
  · intro t ht
    have ht' : φ t ∈ S.image φ := by
      rw [hST]
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    rcases Finset.mem_image.mp ht' with ⟨s, hs, hEq⟩
    have hst : s = t := hφ hEq
    simpa [hst] using hs

/-- Injective inclusion of images forces inclusion of the original finite
carrier subsets. -/
theorem finset_subset_of_image_subset_of_injective
    {γ : Type w} [DecidableEq γ]
    {δ : Type*} [DecidableEq δ]
    {φ : γ → δ} (hφ : Function.Injective φ)
    {S T : Finset γ}
    (hST : S.image φ ⊆ T.image φ) :
    S ⊆ T := by
  intro s hs
  have hs' : φ s ∈ T.image φ := hST (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  rcases Finset.mem_image.mp hs' with ⟨t, ht, hEq⟩
  exact hφ hEq ▸ ht

/-- If a raw carrier fragment maps to a scanner coordinate clique, injectivity
recovers the raw fragment itself as the corresponding point-coordinate fiber. -/
theorem fragment_eq_pointCoordClique_of_image_mem_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {φ : γ → AtomClass cell.F}
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective φ)
    (himage : ∀ g r, (pointCoordClique g r).image φ = coordClique cell P g r)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    {F : Finset γ}
    (hF : F.image φ ∈ coordCliques cell P) :
    ∃ g ∈ P, ∃ p, F = pointCoordClique g (SameSupportCell.rho_g cell g (φ p)) := by
  classical
  rcases Finset.mem_biUnion.mp hF with ⟨g, hg, hFg⟩
  rcases Finset.mem_image.mp hFg with ⟨r, hr, hEqImage⟩
  rw [pi_h] at hr
  rcases Finset.mem_image.mp hr with ⟨A, hA, hAr⟩
  rcases hsurj A hA with ⟨p, hp⟩
  have hImage' : F.image φ = (pointCoordClique g r).image φ := by
    calc
      F.image φ = coordClique cell P g r := hEqImage.symm
      _ = (pointCoordClique g r).image φ := (himage g r).symm
  have hEq : F = pointCoordClique g r :=
    finset_eq_of_image_eq_image_of_injective hφ hImage'
  refine ⟨g, hg, p, ?_⟩
  have hRho : SameSupportCell.rho_g cell g (φ p) = r := by
    calc
      SameSupportCell.rho_g cell g (φ p) = SameSupportCell.rho_g cell g A := by rw [hp]
      _ = r := hAr
  rw [hEq, hRho]

/-- Scanner-side domination by images of raw carrier fragments transports back
to domination of the underlying point-coordinate fibers under an injective
carrier map. -/
theorem pointCoordClique_dominated_by_raw_of_coordCliques_dominated
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective φ)
    (himage : ∀ g r, (pointCoordClique g r).image φ = coordClique cell P g r)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ raw ∈ frags, C ⊆ raw.image φ) :
    ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags,
        pointCoordClique g (SameSupportCell.rho_g cell g (φ p)) ⊆ raw := by
  classical
  intro g hg p
  let r := SameSupportCell.rho_g cell g (φ p)
  have hC : coordClique cell P g r ∈ coordCliques cell P := by
    exact coordClique_mem_coordCliques_of_class_witness cell P hg (hmem p) rfl
  rcases hdom (coordClique cell P g r) hC with ⟨raw, hraw, hsub⟩
  refine ⟨raw, hraw, ?_⟩
  apply finset_subset_of_image_subset_of_injective hφ
  intro A hA
  have hA' : A ∈ coordClique cell P g r := by
    simpa [r, himage g r] using hA
  exact hsub hA'

/-- Carrier-side domination of every occupied coordinate fiber transports to
scanner-side domination of every coordinate clique. This abstracts the common
generated `Domination.lean` proof shape. -/
theorem coordCliques_dominated_by_carrierFrags_of_carrierCoordClique_dominated
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hdom : ∀ g r : ℕ, g ∈ P → (∃ p, rho g p = r) →
      ∃ raw ∈ frags, carrierCoordClique rho g r ⊆ raw) :
    ∀ C ∈ coordCliques cell P, ∃ raw ∈ frags, C ⊆ raw.image φ := by
  classical
  intro C hC
  rcases Finset.mem_biUnion.mp hC with ⟨g, hg, hCg⟩
  rcases Finset.mem_image.mp hCg with ⟨r, hr, rfl⟩
  rw [pi_h] at hr
  rcases Finset.mem_image.mp hr with ⟨A, hA, hAr⟩
  rcases hsurj A hA with ⟨p, hp⟩
  have hRho : rho g p = r := by
    calc
      rho g p = SameSupportCell.rho_g cell g (φ p) := (hrho g p).symm
      _ = SameSupportCell.rho_g cell g A := by rw [hp]
      _ = r := hAr
  rcases hdom g r hg ⟨p, hRho⟩ with ⟨raw, hraw, hsub⟩
  refine ⟨raw, hraw, ?_⟩
  rw [← carrierCoordClique_image_eq_coordClique cell P φ rho g r
    hmem hsurj (fun p => hrho g p)]
  exact Finset.image_subset_image hsub

/-- Point-indexed carrier-side domination of occupied coordinate fibers
transports to scanner-side domination of every coordinate clique. -/
theorem coordCliques_dominated_by_carrierFrags_of_occupied_carrierCoordClique_dominated
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, carrierCoordClique rho g (rho g p) ⊆ raw) :
    ∀ C ∈ coordCliques cell P, ∃ raw ∈ frags, C ⊆ raw.image φ := by
  exact coordCliques_dominated_by_carrierFrags_of_carrierCoordClique_dominated
    cell P hmem hsurj hrho (by
      intro g r hg hocc
      rcases hocc with ⟨p, hp⟩
      rcases hdom g hg p with ⟨raw, hraw, hsub⟩
      exact ⟨raw, hraw, by simpa [hp] using hsub⟩)

/-- If every carrier fragment is an occupied carrier coordinate fiber, then
its transported image is a scanner coordinate clique. This abstracts the common
generated `Subfamily.lean` proof shape. -/
theorem fragment_image_mem_coordCliques_of_eq_carrierCoordClique
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags,
      ∃ g ∈ P, ∃ r : ℕ, F = carrierCoordClique rho g r ∧
        ∃ p, rho g p = r) :
    ∀ F ∈ frags, F.image φ ∈ coordCliques cell P := by
  classical
  intro F hF
  rcases hfrag F hF with ⟨g, hg, r, hEq, p, hp⟩
  have hImage : F.image φ = coordClique cell P g r := by
    rw [hEq]
    exact carrierCoordClique_image_eq_coordClique cell P φ rho g r
      hmem hsurj (fun p => hrho g p)
  rw [hImage]
  exact coordClique_mem_coordCliques_of_class_witness cell P hg
    (hmem p) ((hrho g p).trans hp)

/-- Point-indexed version of
`fragment_image_mem_coordCliques_of_eq_carrierCoordClique`, avoiding an
explicit existential residue. -/
theorem fragment_image_mem_coordCliques_of_eq_occupied_carrierCoordClique
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags,
      ∃ g ∈ P, ∃ p, F = carrierCoordClique rho g (rho g p)) :
    ∀ F ∈ frags, F.image φ ∈ coordCliques cell P := by
  exact fragment_image_mem_coordCliques_of_eq_carrierCoordClique
    cell P hmem hsurj hrho (by
      intro F hF
      rcases hfrag F hF with ⟨g, hg, p, hEq⟩
      exact ⟨g, hg, rho g p, hEq, p, rfl⟩)

/-- Scanner-facing reduced-class bridge: if every generated carrier fragment
maps to a coordinate clique, and every coordinate clique is contained in the
image of some generated carrier fragment, then an injective carrier-side
two-axis certificate gives the scanner-side two-axis certificate shape. -/
theorem twoAxisCertificateShape_of_fragment_images_subset_dominated_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hsub : ∀ F ∈ frags, F.image φ ∈ coordCliques cell P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ frags, C ⊆ F.image φ)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    TwoAxisCertificateShape cell P := by
  exact twoAxisCertificateShape_of_imageFrags_subset_dominated_coordCliques
    cell P hφ
    (imageFrags_subset_coordCliques_of_forall_image_mem cell P hsub)
    (coordCliques_dominated_by_imageFrags_of_forall_image_dominated cell P hdom)
    hw

/-- Named finite data package for the reduced-class scanner bridge. A row
instantiates this structure by giving an injective scanner carrier, a reduced
fragment family whose images are coordinate cliques, domination of every raw
coordinate clique by one reduced fragment image, and a two-axis certificate on
the carrier fragments. -/
structure ReducedTwoAxisScannerBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (γ : Type w) [DecidableEq γ]
    (frags : Finset (Finset γ)) (φ : γ → AtomClass cell.F) where
  phi_injective : Function.Injective φ
  fragment_image_mem : ∀ F ∈ frags, F.image φ ∈ coordCliques cell P
  coord_dominated : ∀ C ∈ coordCliques cell P, ∃ F ∈ frags, C ⊆ F.image φ
  certificate : Nonempty (TwoAxisCertificate frags)

/-- Named occupied-carrier bridge data for the reduced scanner branch. This is
the smallest source-level package matching the finite scanner hypotheses that
remain to be derived uniformly from the dyadic reduced-class construction. -/
structure OccupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (γ : Type w) [Fintype γ] [DecidableEq γ]
    (frags : Finset (Finset γ)) (φ : γ → AtomClass cell.F) (rho : ℕ → γ → ℕ)
    where
  phi_injective : Function.Injective φ
  point_mem_X_P : ∀ p, φ p ∈ X_P cell.label cell.F P
  surjective_on_X_P : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A
  rho_compat : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p
  fragment_eq : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = carrierCoordClique rho g (rho g p)
  dominated : ∀ g : ℕ, g ∈ P → ∀ p,
    ∃ raw ∈ frags, carrierCoordClique rho g (rho g p) ⊆ raw
  certificate : Nonempty (TwoAxisCertificate frags)

/-- Build the named occupied-carrier scanner bridge directly from its row-facing
hypotheses. This is the common constructor shared by the closed scanner rows. -/
def occupiedCarrierReducedTwoAxisBridge_of_occupied_carrierCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = carrierCoordClique rho g (rho g p))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, carrierCoordClique rho g (rho g p) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho where
  phi_injective := hφ
  point_mem_X_P := hmem
  surjective_on_X_P := hsurj
  rho_compat := hrho
  fragment_eq := hfrag
  dominated := hdom
  certificate := hw

/-- Build the named occupied-carrier scanner bridge from point-indexed
coordinate fibers, together with a source-level proof that those fibers are the
carrier coordinate cliques used by the bridge. This absorbs the last trivial
point-to-carrier conversion shared by the closed scanner rows. -/
def occupiedCarrierReducedTwoAxisBridge_of_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (pointCoordClique : ℕ → γ → Finset γ)
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hpoint : ∀ g p, pointCoordClique g p = carrierCoordClique rho g (rho g p))
    (hfrag : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g p)
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p, ∃ raw ∈ frags, pointCoordClique g p ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho :=
  occupiedCarrierReducedTwoAxisBridge_of_occupied_carrierCoordClique_fragments
    cell P hφ hmem hsurj hrho
    (by
      intro F hF
      rcases hfrag F hF with ⟨g, hg, p, hEq⟩
      exact ⟨g, hg, p, by rw [hEq, hpoint g p]⟩)
    (by
      intro g hg p
      rcases hdom g hg p with ⟨raw, hraw, hsub⟩
      exact ⟨raw, hraw, by simpa [hpoint g p] using hsub⟩)
    hw

/-- Reduced two-axis scanner certificate shape for the dyadic conjecture. This
is the finite carrier/data version of the two-axis branch used by scanner-side
reduced residue rows. -/
def ReducedTwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ) :
    Prop := by
  classical
  exact ∃ (γ : Type w) (inst : DecidableEq γ),
    letI : DecidableEq γ := inst
    ∃ (frags : Finset (Finset γ)) (φ : γ → AtomClass cell.F),
      ReducedTwoAxisScannerBridge cell P γ frags φ

/-- Sharper scanner-facing certificate-shape conjecture: the two-axis branch
is required to come through the reduced finite scanner bridge rather than an
arbitrary already-transported certificate on `coordCliques`. -/
def DyadicScannerCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ) :
    Prop := by
  classical
  exact WholeAxisCertificate cell P ∨
    ReducedTwoAxisCertificateShape.{u, v, w} cell P ∨
    hasCornerClusterCarrierAET cell P

/-- A named reduced-class scanner bridge inhabits the two-axis branch. -/
theorem twoAxisCertificateShape_of_reducedTwoAxisScannerBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (B : ReducedTwoAxisScannerBridge cell P γ frags φ) :
    TwoAxisCertificateShape cell P := by
  exact twoAxisCertificateShape_of_fragment_images_subset_dominated_coordCliques
    cell P B.phi_injective B.fragment_image_mem B.coord_dominated B.certificate

/-- A named reduced-class scanner bridge inhabits the existential reduced
scanner certificate branch. -/
theorem reducedTwoAxisCertificateShape_of_reducedTwoAxisScannerBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (B : ReducedTwoAxisScannerBridge cell P γ frags φ) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact ⟨γ, inferInstance, frags, φ, B⟩

/-- Occupied-carrier bridge data canonically supplies the older reduced scanner
bridge by transporting fragment classification and domination to the scanner
surface. -/
theorem reducedTwoAxisScannerBridge_of_occupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (B : OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho) :
    ReducedTwoAxisScannerBridge cell P γ frags φ where
  phi_injective := B.phi_injective
  fragment_image_mem :=
    fragment_image_mem_coordCliques_of_eq_occupied_carrierCoordClique
      cell P B.point_mem_X_P B.surjective_on_X_P B.rho_compat B.fragment_eq
  coord_dominated :=
    coordCliques_dominated_by_carrierFrags_of_occupied_carrierCoordClique_dominated
      cell P B.point_mem_X_P B.surjective_on_X_P B.rho_compat B.dominated
  certificate := B.certificate

/-- A named occupied-carrier bridge inhabits the scanner-facing two-axis
certificate branch. -/
theorem twoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (B : OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho) :
    TwoAxisCertificateShape cell P := by
  exact twoAxisCertificateShape_of_reducedTwoAxisScannerBridge cell P
    (reducedTwoAxisScannerBridge_of_occupiedCarrierReducedTwoAxisBridge cell P B)

/-- A named occupied-carrier bridge inhabits the existential reduced scanner
certificate branch. -/
theorem reducedTwoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (B : OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_reducedTwoAxisScannerBridge cell P
    (reducedTwoAxisScannerBridge_of_occupiedCarrierReducedTwoAxisBridge cell P B)

/-- Source-level reduced scanner facts inhabit the existential reduced scanner
certificate branch. -/
theorem reducedTwoAxisCertificateShape_of_fragment_images_subset_dominated_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hsub : ∀ F ∈ frags, F.image φ ∈ coordCliques cell P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ frags, C ⊆ F.image φ)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_reducedTwoAxisScannerBridge cell P
    ({ phi_injective := hφ
       fragment_image_mem := hsub
       coord_dominated := hdom
       certificate := hw } :
      ReducedTwoAxisScannerBridge cell P γ frags φ)

/-- Carrier-coordinate fragment hypotheses give the reduced scanner
certificate branch. This is the compact structural interface for reduced
two-axis scanner rows. -/
theorem reducedTwoAxisCertificateShape_of_carrierCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags,
      ∃ g ∈ P, ∃ r : ℕ, F = carrierCoordClique rho g r ∧
        ∃ p, rho g p = r)
    (hdom : ∀ g r : ℕ, g ∈ P → (∃ p, rho g p = r) →
      ∃ raw ∈ frags, carrierCoordClique rho g r ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_fragment_images_subset_dominated_coordCliques
    cell P hφ
    (fragment_image_mem_coordCliques_of_eq_carrierCoordClique
      cell P hmem hsurj hrho hfrag)
    (coordCliques_dominated_by_carrierFrags_of_carrierCoordClique_dominated
      cell P hmem hsurj hrho hdom)
    hw

/-- Point-indexed carrier-coordinate fragment hypotheses give the reduced
scanner certificate branch. This is the finite scanner-friendly form of the
compact structural interface. -/
theorem reducedTwoAxisCertificateShape_of_occupied_carrierCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags,
      ∃ g ∈ P, ∃ p, F = carrierCoordClique rho g (rho g p))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, carrierCoordClique rho g (rho g p) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
    cell P
    ({ phi_injective := hφ
       point_mem_X_P := hmem
       surjective_on_X_P := hsurj
       rho_compat := hrho
       fragment_eq := hfrag
       dominated := hdom
       certificate := hw } :
      OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho)

/-- Point-indexed fragment hypotheses give the reduced scanner certificate
branch directly. This is the source-level theorem surface used by the closed
scanner rows. -/
theorem reducedTwoAxisCertificateShape_of_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (pointCoordClique : ℕ → γ → Finset γ)
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hpoint : ∀ g p, pointCoordClique g p = carrierCoordClique rho g (rho g p))
    (hfrag : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g p)
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p, ∃ raw ∈ frags, pointCoordClique g p ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
    cell P
    (occupiedCarrierReducedTwoAxisBridge_of_pointCoordClique_fragments
      cell P pointCoordClique hφ hmem hsurj hrho hpoint hfrag hdom hw)

/-- If the point carrier covers exactly the `P`-support fiber, then the
point-indexed fragment hypotheses already give the reduced scanner certificate
branch directly. This absorbs the routine `X_P` transport shared by the closed
scanner rows. -/
theorem reducedTwoAxisCertificateShape_of_support_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)}
    (pointAtom : γ → α)
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective (fun p => atomClass cell.F (pointAtom p)))
    (hsupport :
      ∀ p, ModularSchur.CoordinateUnion.supportLabels cell.label cell.F (pointAtom p) = P)
    (hsurj :
      ∀ a : α,
        ModularSchur.CoordinateUnion.supportLabels cell.label cell.F a = P →
          ∃ p, pointAtom p = a)
    (hpoint :
      ∀ g r,
        pointCoordClique g r =
          carrierCoordClique (fun g p => cell.rho g (pointAtom p)) g r)
    (hfrag :
      ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g (cell.rho g (pointAtom p)))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, pointCoordClique g (cell.rho g (pointAtom p)) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_pointCoordClique_fragments
    cell P
    (φ := fun p => atomClass cell.F (pointAtom p))
    (rho := fun g p => cell.rho g (pointAtom p))
    (fun g p => pointCoordClique g (cell.rho g (pointAtom p)))
    hφ
    (atomClass_mem_X_P_of_support cell P pointAtom hsupport)
    (atomClass_surjective_on_X_P_of_support cell P pointAtom hsurj)
    (by
      intro g p
      simp [SameSupportCell.rho_g_mk])
    (by
      intro g p
      simpa using hpoint g (cell.rho g (pointAtom p)))
    hfrag
    hdom
    hw

/-- A witness-form domination theorem is enough for the reduced scanner
certificate once the point carrier covers the `P`-support fiber. This matches
the natural output of the generated domination modules. -/
theorem reducedTwoAxisCertificateShape_of_support_pointCoordClique_witnessed_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)}
    (pointAtom : γ → α)
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective (fun p => atomClass cell.F (pointAtom p)))
    (hsupport :
      ∀ p, ModularSchur.CoordinateUnion.supportLabels cell.label cell.F (pointAtom p) = P)
    (hsurj :
      ∀ a : α,
        ModularSchur.CoordinateUnion.supportLabels cell.label cell.F a = P →
          ∃ p, pointAtom p = a)
    (hpoint :
      ∀ g r,
        pointCoordClique g r =
          carrierCoordClique (fun g p => cell.rho g (pointAtom p)) g r)
    (hfrag :
      ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g (cell.rho g (pointAtom p)))
    (hdom :
      ∀ g r : ℕ, g ∈ P →
        (∃ p : γ, cell.rho g (pointAtom p) = r) →
        ∃ raw ∈ frags, pointCoordClique g r ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_support_pointCoordClique_fragments
    cell P pointAtom pointCoordClique hφ hsupport hsurj hpoint hfrag
    (by
      intro g hg p
      exact hdom g (cell.rho g (pointAtom p)) hg ⟨p, rfl⟩)
    hw

/-- If the generated raw fragments already map to coordinate cliques and every
coordinate clique is dominated by a raw fragment image, then the occupied-point
fragment and domination witnesses are derivable source-side from support and
surjectivity alone. -/
theorem reducedTwoAxisCertificateShape_of_support_pointCoordClique_images_dominated
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)}
    (pointAtom : γ → α)
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective (fun p => atomClass cell.F (pointAtom p)))
    (hsupport :
      ∀ p, ModularSchur.CoordinateUnion.supportLabels cell.label cell.F (pointAtom p) = P)
    (hsurj :
      ∀ a : α,
        ModularSchur.CoordinateUnion.supportLabels cell.label cell.F a = P →
          ∃ p, pointAtom p = a)
    (hpoint :
      ∀ g r,
        pointCoordClique g r =
          carrierCoordClique (fun g p => cell.rho g (pointAtom p)) g r)
    (hsub :
      ∀ F ∈ frags,
        F.image (fun p => atomClass cell.F (pointAtom p)) ∈ coordCliques cell P)
    (hdom :
      ∀ C ∈ coordCliques cell P,
        ∃ raw ∈ frags, C ⊆ raw.image (fun p => atomClass cell.F (pointAtom p)))
    (hw : Nonempty (TwoAxisCertificate frags)) :
    ReducedTwoAxisCertificateShape.{u, v, w} cell P := by
  exact reducedTwoAxisCertificateShape_of_support_pointCoordClique_witnessed_fragments
    cell P pointAtom pointCoordClique hφ hsupport hsurj hpoint
    (by
      intro F hF
      exact fragment_eq_pointCoordClique_of_image_mem_coordCliques
        cell P pointCoordClique hφ
        (by
          intro g r
          rw [hpoint g r]
          simpa using atomClass_pointCoordClique_image_eq_coordClique
            cell P pointAtom hsupport hsurj g r)
        (atomClass_surjective_on_X_P_of_support cell P pointAtom hsurj)
        (hsub F hF))
    (by
      intro g r hg hr
      let hdomRaw :=
        pointCoordClique_dominated_by_raw_of_coordCliques_dominated
          (cell := cell) (P := P)
          (pointCoordClique := pointCoordClique)
          (hφ := hφ)
          (himage := by
            intro g r
            rw [hpoint g r]
            simpa using atomClass_pointCoordClique_image_eq_coordClique
              cell P pointAtom hsupport hsurj g r)
          (hmem := atomClass_mem_X_P_of_support cell P pointAtom hsupport)
          (hdom := hdom)
      rcases hr with ⟨p, hp⟩
      rcases hdomRaw g hg p with ⟨raw, hraw, hsub⟩
      refine ⟨raw, hraw, ?_⟩
      simpa [hp] using hsub)
    hw

/-- The existential reduced scanner bridge shape inhabits the two-axis
certificate branch. -/
theorem twoAxisCertificateShape_of_ReducedTwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : ReducedTwoAxisCertificateShape.{u, v, w} cell P) :
    TwoAxisCertificateShape cell P := by
  rcases h with ⟨γ, inst, frags, φ, B⟩
  letI : DecidableEq γ := inst
  exact twoAxisCertificateShape_of_reducedTwoAxisScannerBridge cell P B

/-- The two-axis branch injects into the full dyadic certificate shape. -/
theorem dyadicCertificateShape_of_TwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : TwoAxisCertificateShape cell P) :
    DyadicCertificateShape cell P := by
  exact Or.inr (Or.inl h)

/-- A concrete two-axis certificate on `coordCliques` gives the full dyadic
certificate shape through the two-axis branch. -/
theorem dyadicCertificateShape_of_twoAxisCertificate
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (w : TwoAxisCertificate (coordCliques cell P)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_certificate cell P w)

/-- Fragment-family transport followed by injection into the full dyadic
certificate shape. -/
theorem dyadicCertificateShape_of_frags_eq_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {frags : Finset (Finset (AtomClass cell.F))}
    (hfrags : frags = coordCliques cell P)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_frags_eq_coordCliques cell P hfrags hw)

/-- Injective point-carrier transport followed by injection into the full
dyadic certificate shape. -/
theorem dyadicCertificateShape_of_imageFrags_eq_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hfrags : imageFrags φ frags = coordCliques cell P)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_imageFrags_eq_coordCliques cell P hφ hfrags hw)

/-- Dominated-family injective point-carrier transport followed by injection
into the full dyadic certificate shape. -/
theorem dyadicCertificateShape_of_imageFrags_subset_dominated_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hsub : imageFrags φ frags ⊆ coordCliques cell P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ imageFrags φ frags, C ⊆ F)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_imageFrags_subset_dominated_coordCliques
      cell P hφ hsub hdom hw)

/-- Source-level reduced-class bridge followed by injection into the full
dyadic certificate shape. -/
theorem dyadicCertificateShape_of_fragment_images_subset_dominated_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hsub : ∀ F ∈ frags, F.image φ ∈ coordCliques cell P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ frags, C ⊆ F.image φ)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_fragment_images_subset_dominated_coordCliques
      cell P hφ hsub hdom hw)

/-- A named reduced-class scanner bridge gives the full dyadic certificate
shape through the two-axis branch. -/
theorem dyadicCertificateShape_of_reducedTwoAxisScannerBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (B : ReducedTwoAxisScannerBridge cell P γ frags φ) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_reducedTwoAxisScannerBridge cell P B)

/-- The existential reduced scanner bridge shape gives the full dyadic
certificate shape through the two-axis branch. -/
theorem dyadicCertificateShape_of_ReducedTwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : ReducedTwoAxisCertificateShape.{u, v, w} cell P) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_ReducedTwoAxisCertificateShape cell P h)

/-- Whole-axis certificates inhabit the sharper scanner-facing disjunction. -/
theorem dyadicScannerCertificateShape_of_WholeAxisCertificate
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : WholeAxisCertificate cell P) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact Or.inl h

/-- Reduced scanner bridge certificates inhabit the sharper scanner-facing
disjunction. -/
theorem dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : ReducedTwoAxisCertificateShape.{u, v, w} cell P) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact Or.inr (Or.inl h)

/-- Carrier-backed AET certificates inhabit the sharper scanner-facing
disjunction. -/
theorem dyadicScannerCertificateShape_of_hasCornerClusterCarrierAET
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : hasCornerClusterCarrierAET cell P) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact Or.inr (Or.inr h)

/-- A named reduced-class scanner bridge gives the sharper scanner-facing
certificate shape. -/
theorem dyadicScannerCertificateShape_of_reducedTwoAxisScannerBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (B : ReducedTwoAxisScannerBridge cell P γ frags φ) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_reducedTwoAxisScannerBridge cell P B)

/-- A named occupied-carrier bridge gives the sharper scanner-facing
certificate shape. -/
theorem dyadicScannerCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (B : OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
      cell P B)

/-- A named occupied-carrier bridge gives the broader dyadic certificate
shape directly. -/
theorem dyadicCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (B : OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
      cell P B)

/-- A named occupied-carrier bridge gives exactness directly. -/
theorem axis_cover_eq_maxPacking_of_occupiedCarrierReducedTwoAxisBridge
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (B : OccupiedCarrierReducedTwoAxisBridge cell P γ frags φ rho) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  exact axis_cover_eq_maxPacking_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge
      cell P B)

/-- Point-indexed fragment hypotheses give the broader dyadic certificate
shape directly. -/
theorem dyadicCertificateShape_of_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (pointCoordClique : ℕ → γ → Finset γ)
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hpoint : ∀ g p, pointCoordClique g p = carrierCoordClique rho g (rho g p))
    (hfrag : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g p)
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p, ∃ raw ∈ frags, pointCoordClique g p ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_pointCoordClique_fragments
      cell P pointCoordClique hφ hmem hsurj hrho hpoint hfrag hdom hw)

/-- If the point carrier covers exactly the `P`-support fiber, then the
point-indexed fragment hypotheses already give the broader dyadic certificate
shape directly. -/
theorem dyadicCertificateShape_of_support_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)}
    (pointAtom : γ → α)
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective (fun p => atomClass cell.F (pointAtom p)))
    (hsupport :
      ∀ p, ModularSchur.CoordinateUnion.supportLabels cell.label cell.F (pointAtom p) = P)
    (hsurj :
      ∀ a : α,
        ModularSchur.CoordinateUnion.supportLabels cell.label cell.F a = P →
          ∃ p, pointAtom p = a)
    (hpoint :
      ∀ g r,
        pointCoordClique g r =
          carrierCoordClique (fun g p => cell.rho g (pointAtom p)) g r)
    (hfrag :
      ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g (cell.rho g (pointAtom p)))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, pointCoordClique g (cell.rho g (pointAtom p)) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicCertificateShape cell P := by
  exact dyadicCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_support_pointCoordClique_fragments
      cell P pointAtom pointCoordClique hφ hsupport hsurj hpoint hfrag hdom hw)

/-- Point-indexed fragment hypotheses give exactness directly. -/
theorem axis_cover_eq_maxPacking_of_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (pointCoordClique : ℕ → γ → Finset γ)
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hpoint : ∀ g p, pointCoordClique g p = carrierCoordClique rho g (rho g p))
    (hfrag : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g p)
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p, ∃ raw ∈ frags, pointCoordClique g p ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  exact axis_cover_eq_maxPacking_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_occupiedCarrierReducedTwoAxisBridge cell P
      (occupiedCarrierReducedTwoAxisBridge_of_pointCoordClique_fragments
        cell P pointCoordClique hφ hmem hsurj hrho hpoint hfrag hdom hw))

/-- If the point carrier covers exactly the `P`-support fiber, then the
point-indexed fragment hypotheses already give exactness directly. -/
theorem axis_cover_eq_maxPacking_of_support_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)}
    (pointAtom : γ → α)
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective (fun p => atomClass cell.F (pointAtom p)))
    (hsupport :
      ∀ p, ModularSchur.CoordinateUnion.supportLabels cell.label cell.F (pointAtom p) = P)
    (hsurj :
      ∀ a : α,
        ModularSchur.CoordinateUnion.supportLabels cell.label cell.F a = P →
          ∃ p, pointAtom p = a)
    (hpoint :
      ∀ g r,
        pointCoordClique g r =
          carrierCoordClique (fun g p => cell.rho g (pointAtom p)) g r)
    (hfrag :
      ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g (cell.rho g (pointAtom p)))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, pointCoordClique g (cell.rho g (pointAtom p)) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  exact axis_cover_eq_maxPacking_of_TwoAxisCertificateShape cell P
    (twoAxisCertificateShape_of_ReducedTwoAxisCertificateShape cell P
      (reducedTwoAxisCertificateShape_of_support_pointCoordClique_fragments
        cell P pointAtom pointCoordClique hφ hsupport hsurj hpoint hfrag hdom hw))

/-- Source-level reduced scanner facts give the sharper scanner-facing
certificate shape. -/
theorem dyadicScannerCertificateShape_of_fragment_images_subset_dominated_coordCliques
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    (hφ : Function.Injective φ)
    (hsub : ∀ F ∈ frags, F.image φ ∈ coordCliques cell P)
    (hdom : ∀ C ∈ coordCliques cell P, ∃ F ∈ frags, C ⊆ F.image φ)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_fragment_images_subset_dominated_coordCliques
      cell P hφ hsub hdom hw)

/-- Carrier-coordinate fragment hypotheses give the sharper scanner-facing
certificate shape. -/
theorem dyadicScannerCertificateShape_of_carrierCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags,
      ∃ g ∈ P, ∃ r : ℕ, F = carrierCoordClique rho g r ∧
        ∃ p, rho g p = r)
    (hdom : ∀ g r : ℕ, g ∈ P → (∃ p, rho g p = r) →
      ∃ raw ∈ frags, carrierCoordClique rho g r ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_carrierCoordClique_fragments
      cell P hφ hmem hsurj hrho hfrag hdom hw)

/-- Point-indexed carrier-coordinate fragment hypotheses give the sharper
scanner-facing certificate shape. -/
theorem dyadicScannerCertificateShape_of_occupied_carrierCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hfrag : ∀ F ∈ frags,
      ∃ g ∈ P, ∃ p, F = carrierCoordClique rho g (rho g p))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, carrierCoordClique rho g (rho g p) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_occupied_carrierCoordClique_fragments
      cell P hφ hmem hsurj hrho hfrag hdom hw)

/-- Point-indexed fragment hypotheses give the sharper scanner-facing
certificate shape directly. -/
theorem dyadicScannerCertificateShape_of_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)} {φ : γ → AtomClass cell.F}
    {rho : ℕ → γ → ℕ}
    (pointCoordClique : ℕ → γ → Finset γ)
    (hφ : Function.Injective φ)
    (hmem : ∀ p, φ p ∈ X_P cell.label cell.F P)
    (hsurj : ∀ A ∈ X_P cell.label cell.F P, ∃ p, φ p = A)
    (hrho : ∀ g p, SameSupportCell.rho_g cell g (φ p) = rho g p)
    (hpoint : ∀ g p, pointCoordClique g p = carrierCoordClique rho g (rho g p))
    (hfrag : ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g p)
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p, ∃ raw ∈ frags, pointCoordClique g p ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_pointCoordClique_fragments
      cell P pointCoordClique hφ hmem hsurj hrho hpoint hfrag hdom hw)

/-- If the point carrier covers exactly the `P`-support fiber, then the
point-indexed fragment hypotheses already give the sharper scanner-facing
certificate shape directly. -/
theorem dyadicScannerCertificateShape_of_support_pointCoordClique_fragments
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    {γ : Type w} [Fintype γ] [DecidableEq γ]
    {frags : Finset (Finset γ)}
    (pointAtom : γ → α)
    (pointCoordClique : ℕ → ℕ → Finset γ)
    (hφ : Function.Injective (fun p => atomClass cell.F (pointAtom p)))
    (hsupport :
      ∀ p, ModularSchur.CoordinateUnion.supportLabels cell.label cell.F (pointAtom p) = P)
    (hsurj :
      ∀ a : α,
        ModularSchur.CoordinateUnion.supportLabels cell.label cell.F a = P →
          ∃ p, pointAtom p = a)
    (hpoint :
      ∀ g r,
        pointCoordClique g r =
          carrierCoordClique (fun g p => cell.rho g (pointAtom p)) g r)
    (hfrag :
      ∀ F ∈ frags, ∃ g ∈ P, ∃ p, F = pointCoordClique g (cell.rho g (pointAtom p)))
    (hdom : ∀ g : ℕ, g ∈ P → ∀ p,
      ∃ raw ∈ frags, pointCoordClique g (cell.rho g (pointAtom p)) ⊆ raw)
    (hw : Nonempty (TwoAxisCertificate frags)) :
    DyadicScannerCertificateShape.{u, v, w} cell P := by
  exact dyadicScannerCertificateShape_of_ReducedTwoAxisCertificateShape cell P
    (reducedTwoAxisCertificateShape_of_support_pointCoordClique_fragments
      cell P pointAtom pointCoordClique hφ hsupport hsurj hpoint hfrag hdom hw)

/-- The sharper scanner-facing certificate shape implies the broader dyadic
certificate shape. -/
theorem dyadicCertificateShape_of_DyadicScannerCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : DyadicScannerCertificateShape.{u, v, w} cell P) :
    DyadicCertificateShape cell P := by
  rcases h with hWhole | hReduced | hAET
  · exact Or.inl hWhole
  · exact dyadicCertificateShape_of_ReducedTwoAxisCertificateShape cell P hReduced
  · exact Or.inr (Or.inr hAET)

/-- The dyadic certificate-shape conjecture would immediately imply exactness. -/
theorem axis_cover_eq_maxPacking_of_DyadicCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : DyadicCertificateShape cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  classical
  rcases h with h | h | h
  · exact axis_cover_eq_maxPacking_of_WholeAxisCertificate cell P h
  · exact axis_cover_eq_maxPacking_of_TwoAxisCertificateShape cell P h
  · exact axis_cover_eq_maxPacking_of_hasCornerClusterCarrierAET cell h

/-- The sharper scanner-facing certificate-shape conjecture also immediately
implies exactness. -/
theorem axis_cover_eq_maxPacking_of_DyadicScannerCertificateShape
    (cell : NormalizedCell α ι) [Fintype (AtomClass cell.F)] (P : Finset ℕ)
    (h : DyadicScannerCertificateShape.{u, v, w} cell P) :
    axis_cover (coordCliques cell P) = maxPacking (coordCliques cell P) := by
  exact axis_cover_eq_maxPacking_of_DyadicCertificateShape cell P
    (dyadicCertificateShape_of_DyadicScannerCertificateShape cell P h)

end ModularSchur.DeficitGrowth
