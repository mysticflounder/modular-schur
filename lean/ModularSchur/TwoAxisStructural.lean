import ModularSchur.ResidueAxis
import ModularSchur.TauClosure

/-!
# Two-axis structural certificate

This module is the first Lean skeleton for the deficit-growth two-axis
structural theorem. It does not mention any generated row. Instead, it packages
the abstract cover/packing data that the row descriptors expose and routes the
conclusion through the generic exact-duality theorem in `ResidueAxis`.
-/

namespace ModularSchur.TwoAxisStructural

open Finset
open ModularSchur.ResidueAxis
open ModularSchur.TauClosure

universe u v

variable {α : Type u} [DecidableEq α]

/-- Abstract two-axis certificate: a cover and a packing of equal size. -/
structure TwoAxisCertificate (frags : Finset (Finset α)) where
  cover : Finset (Finset α)
  packing : Finset α
  cover_is_cover : IsCoverOf frags cover
  packing_is_packing : AxisPacking frags packing
  card_eq : cover.card = packing.card

/-- Transport a two-axis certificate across definitional or proved equality of
fragment families. -/
def certificate_of_eq
    {frags frags' : Finset (Finset α)}
    (h : frags = frags') (w : TwoAxisCertificate frags) :
    TwoAxisCertificate frags' := by
  subst h
  exact w

/-- Nonempty two-axis certificates also transport across equality of fragment
families. -/
theorem certificate_nonempty_of_eq
    {frags frags' : Finset (Finset α)}
    (h : frags = frags') (hw : Nonempty (TwoAxisCertificate frags)) :
    Nonempty (TwoAxisCertificate frags') := by
  rcases hw with ⟨w⟩
  exact ⟨certificate_of_eq h w⟩

variable {β : Type v} [DecidableEq β]

/-- Image of a fragment family under a point map. -/
def imageFrags (φ : α → β) (frags : Finset (Finset α)) : Finset (Finset β) :=
  frags.image (fun F => F.image φ)

/-- Injective point maps induce injective maps on finite fragments. -/
theorem finset_image_injective_of_injective {φ : α → β}
    (hφ : Function.Injective φ) :
    Function.Injective (fun F : Finset α => F.image φ) := by
  intro F G hFG
  ext x
  constructor
  · intro hx
    have hφx : φ x ∈ F.image φ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hφxG : φ x ∈ G.image φ := by
      simpa [hFG] using hφx
    rcases Finset.mem_image.mp hφxG with ⟨y, hyG, hy⟩
    have hyx : y = x := hφ hy
    simpa [hyx] using hyG
  · intro hx
    have hφx : φ x ∈ G.image φ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hφxF : φ x ∈ F.image φ := by
      simpa [hFG] using hφx
    rcases Finset.mem_image.mp hφxF with ⟨y, hyF, hy⟩
    have hyx : y = x := hφ hy
    simpa [hyx] using hyF

/-- Covers transport along arbitrary point maps. -/
theorem isCoverOf_image {φ : α → β} {frags cover : Finset (Finset α)}
    (hC : IsCoverOf frags cover) :
    IsCoverOf (imageFrags φ frags) (imageFrags φ cover) := by
  constructor
  · intro F hF
    rcases Finset.mem_image.mp hF with ⟨C, hCmem, rfl⟩
    exact Finset.mem_image.mpr ⟨C, hC.1 hCmem, rfl⟩
  · intro y hy
    rcases Finset.mem_biUnion.mp hy with ⟨F', hF', hyF'⟩
    rcases Finset.mem_image.mp hF' with ⟨F, hFmem, rfl⟩
    rcases Finset.mem_image.mp hyF' with ⟨x, hxF, rfl⟩
    have hxUnion : x ∈ frags.biUnion id := Finset.mem_biUnion.mpr ⟨F, hFmem, hxF⟩
    rcases Finset.mem_biUnion.mp (hC.2 hxUnion) with ⟨C, hCmem, hxC⟩
    exact Finset.mem_biUnion.mpr
      ⟨C.image φ, Finset.mem_image.mpr ⟨C, hCmem, rfl⟩,
        Finset.mem_image.mpr ⟨x, hxC, rfl⟩⟩

/-- Packings transport along injective point maps. -/
theorem axisPacking_image {φ : α → β} (hφ : Function.Injective φ)
    {frags : Finset (Finset α)} {packing : Finset α}
    (hP : AxisPacking frags packing) :
    AxisPacking (imageFrags φ frags) (packing.image φ) := by
  constructor
  · intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hxP, rfl⟩
    rcases Finset.mem_biUnion.mp (hP.subset_union hxP) with ⟨F, hFmem, hxF⟩
    exact Finset.mem_biUnion.mpr
      ⟨F.image φ, Finset.mem_image.mpr ⟨F, hFmem, rfl⟩,
        Finset.mem_image.mpr ⟨x, hxF, rfl⟩⟩
  · intro F' hF'
    rcases Finset.mem_image.mp hF' with ⟨F, hFmem, rfl⟩
    apply Finset.card_le_one.mpr
    intro y hy z hz
    rw [Finset.mem_inter] at hy hz
    rcases Finset.mem_image.mp hy.1 with ⟨x, hxP, rfl⟩
    rcases Finset.mem_image.mp hy.2 with ⟨xF, hxF, hxEq⟩
    have hxinF : x ∈ F := by
      have : xF = x := hφ hxEq
      simpa [this] using hxF
    rcases Finset.mem_image.mp hz.1 with ⟨w, hwP, rfl⟩
    rcases Finset.mem_image.mp hz.2 with ⟨wF, hwF, hwEq⟩
    have hwinF : w ∈ F := by
      have : wF = w := hφ hwEq
      simpa [this] using hwF
    have hxw : x = w :=
      Finset.card_le_one.mp (hP.at_most_one F hFmem)
        x (Finset.mem_inter.mpr ⟨hxP, hxinF⟩)
        w (Finset.mem_inter.mpr ⟨hwP, hwinF⟩)
    simp [hxw]

/-- A two-axis certificate transports along an injective point map. -/
noncomputable def certificate_image {φ : α → β} (hφ : Function.Injective φ)
    {frags : Finset (Finset α)} (w : TwoAxisCertificate frags) :
    TwoAxisCertificate (imageFrags φ frags) :=
  { cover := imageFrags φ w.cover,
    packing := w.packing.image φ,
    cover_is_cover := isCoverOf_image w.cover_is_cover,
    packing_is_packing := axisPacking_image hφ w.packing_is_packing,
    card_eq := by
      calc
        (imageFrags φ w.cover).card = w.cover.card := by
          exact Finset.card_image_of_injOn
            (fun _ _ _ _ h => finset_image_injective_of_injective hφ h)
        _ = w.packing.card := w.card_eq
        _ = (w.packing.image φ).card := by
          exact (Finset.card_image_of_injOn (fun _ _ _ _ h => hφ h)).symm }

/-- Nonempty two-axis certificates transport along an injective point map. -/
theorem certificate_nonempty_image {φ : α → β} (hφ : Function.Injective φ)
    {frags : Finset (Finset α)}
    (hw : Nonempty (TwoAxisCertificate frags)) :
    Nonempty (TwoAxisCertificate (imageFrags φ frags)) := by
  rcases hw with ⟨w⟩
  exact ⟨certificate_image hφ w⟩

/-- A cover of a subfamily also covers a larger family when every larger
fragment is contained in some subfamily fragment. -/
theorem isCoverOf_of_subset_dominated
    {small big cover : Finset (Finset α)}
    (hC : IsCoverOf small cover)
    (hsub : small ⊆ big)
    (hdom : ∀ F ∈ big, ∃ G ∈ small, F ⊆ G) :
    IsCoverOf big cover := by
  constructor
  · intro C hCmem
    exact hsub (hC.1 hCmem)
  · intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨F, hF, hxF⟩
    rcases hdom F hF with ⟨G, hG, hFG⟩
    exact hC.2 (Finset.mem_biUnion.mpr ⟨G, hG, hFG hxF⟩)

/-- A packing against a subfamily remains a packing against a dominated larger
family. -/
theorem axisPacking_of_subset_dominated
    {small big : Finset (Finset α)} {packing : Finset α}
    (hP : AxisPacking small packing)
    (hsub : small ⊆ big)
    (hdom : ∀ F ∈ big, ∃ G ∈ small, F ⊆ G) :
    AxisPacking big packing := by
  constructor
  · intro x hx
    rcases Finset.mem_biUnion.mp (hP.subset_union hx) with ⟨F, hF, hxF⟩
    exact Finset.mem_biUnion.mpr ⟨F, hsub hF, hxF⟩
  · intro F hF
    rcases hdom F hF with ⟨G, hG, hFG⟩
    have hInter : packing ∩ F ⊆ packing ∩ G := by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨hx.1, hFG hx.2⟩
    exact le_trans (Finset.card_le_card hInter) (hP.at_most_one G hG)

/-- A two-axis certificate on a subfamily transports to a dominated larger
family without changing the cover or packing. -/
noncomputable def certificate_of_subset_dominated
    {small big : Finset (Finset α)}
    (hsub : small ⊆ big)
    (hdom : ∀ F ∈ big, ∃ G ∈ small, F ⊆ G)
    (w : TwoAxisCertificate small) :
    TwoAxisCertificate big :=
  { cover := w.cover,
    packing := w.packing,
    cover_is_cover := isCoverOf_of_subset_dominated w.cover_is_cover hsub hdom,
    packing_is_packing :=
      axisPacking_of_subset_dominated w.packing_is_packing hsub hdom,
    card_eq := w.card_eq }

/-- Nonempty two-axis certificates transport across dominated-family
inclusions. -/
theorem certificate_nonempty_of_subset_dominated
    {small big : Finset (Finset α)}
    (hsub : small ⊆ big)
    (hdom : ∀ F ∈ big, ∃ G ∈ small, F ⊆ G)
    (hw : Nonempty (TwoAxisCertificate small)) :
    Nonempty (TwoAxisCertificate big) := by
  rcases hw with ⟨w⟩
  exact ⟨certificate_of_subset_dominated hsub hdom w⟩

/-- The abstract two-axis certificate already forces exact duality. -/
theorem axis_cover_eq_maxPacking_of_certificate
    {frags : Finset (Finset α)} (w : TwoAxisCertificate frags) :
    axis_cover frags = maxPacking frags := by
  exact axis_cover_eq_maxPacking_of_cover_and_packing
    w.cover_is_cover w.packing_is_packing w.card_eq

/-- The same abstract certificate also recovers the cover cardinality. -/
theorem axis_cover_eq_card_of_certificate
    {frags : Finset (Finset α)} (w : TwoAxisCertificate frags) :
    axis_cover frags = w.cover.card := by
  exact axis_cover_eq_card_of_cover_and_packing
    w.cover_is_cover w.packing_is_packing w.card_eq

/-- The packing size is the same witness cardinality. -/
theorem maxPacking_eq_card_of_certificate
    {frags : Finset (Finset α)} (w : TwoAxisCertificate frags) :
    maxPacking frags = w.cover.card := by
  exact (axis_cover_eq_maxPacking_of_certificate (frags := frags) w).symm.trans
    (axis_cover_eq_card_of_certificate (frags := frags) w)

end ModularSchur.TwoAxisStructural
