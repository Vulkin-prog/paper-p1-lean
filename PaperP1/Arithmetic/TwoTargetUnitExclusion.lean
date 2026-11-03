module

public import PaperP1.Arithmetic.TwoTargetClassOffsets
public import PaperP1.Arithmetic.NormalizedUnitCount

/-! # Excluding the actual coordinate labels at all but one unit leaves at most one normalized coincidence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetUnitExclusion

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.TwoTargetWindowSections
  PaperP1.NormalizedUnitCount PaperP1.FiniteEvenSquareClasses

def unitEndpoints {s L : ℕ} (D : Finset (Fin (L + 1) × Fin (L + 1))) :
    Finset (TwoTargetWindowSections.Coordinate s L) :=
  D.image (fun u ↦ (Sum.inr 0, u.1)) ∪ D.image (fun u ↦ (Sum.inr 1, u.2))

def excludedLabels {s L : ℕ} {A : Type*} [DecidableEq A]
    (ℓ : TwoTargetWindowSections.Coordinate s L → A)
    (D : Finset (Fin (L + 1) × Fin (L + 1))) : Finset A := (unitEndpoints D).image ℓ

theorem endpoints_card {s L : ℕ} (D : Finset (Fin (L + 1) × Fin (L + 1))) :
    (unitEndpoints (s := s) D).card ≤ 2 * D.card := by
  have h := (card_union_le (D.image fun u ↦ ((Sum.inr 0, u.1) : TwoTargetWindowSections.Coordinate s L))
    (D.image fun u ↦ ((Sum.inr 1, u.2) : TwoTargetWindowSections.Coordinate s L))).trans
      (Nat.add_le_add card_image_le card_image_le)
  exact h.trans (by omega)

theorem image_labels_card {s L : ℕ} {A : Type*} [DecidableEq A]
    (ℓ : TwoTargetWindowSections.Coordinate s L → A) (D : Finset (Fin (L + 1) × Fin (L + 1))) :
    (excludedLabels ℓ D).card ≤ 2 * D.card := card_image_le.trans (endpoints_card D)

theorem class_avoids_endpoints {s L : ℕ} {A : Type*} [DecidableEq A]
    (ℓ : TwoTargetWindowSections.Coordinate s L → A) (D : Finset (Fin (L + 1) × Fin (L + 1)))
    (α : A) (hα : α ∉ excludedLabels ℓ D) :
    ∀ v ∈ LabelClassPartition.part ℓ α, v ∉ unitEndpoints D := by
  intro v hv hvD
  exact hα (mem_image.mpr ⟨v, hvD, (LabelClassPartition.mem_part _ _ _).mp hv⟩)

theorem except_one {A : Type*} [DecidableEq A] (U : Finset A) :
    ∃ D : Finset A, D ⊆ U ∧ D.card = U.card - 1 ∧ (U \ D).card ≤ 1 := by
  by_cases hne : U.Nonempty
  · obtain ⟨u, hu⟩ := hne
    refine ⟨U.erase u, erase_subset _ _, card_erase_of_mem hu, card_le_one.mpr ?_⟩
    intro x hx y hy
    have hxU := (mem_sdiff.mp hx).1
    have hyU := (mem_sdiff.mp hy).1
    have hxu : x = u := by
      by_contra h
      exact (mem_sdiff.mp hx).2 (mem_erase.mpr ⟨h, hxU⟩)
    have hyu : y = u := by
      by_contra h
      exact (mem_sdiff.mp hy).2 (mem_erase.mpr ⟨h, hyU⟩)
    exact hxu.trans hyu.symm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact ⟨∅, empty_subset _, by simp, by simp⟩

theorem selected_overlap_le_one {a b y z L : ℕ} (I J : Finset (Fin (L + 1)))
    (D : Finset (Fin (L + 1) × Fin (L + 1)))
    (hremaining : (units a b y z L \ D).card ≤ 1)
    (havoid : ∀ u ∈ D, u.1 ∉ I ∨ u.2 ∉ J) :
    (dilate b (I.image (startCompleteVertexLabel y L)) ∩
      dilate a (J.image (startCompleteVertexLabel z L))).card ≤ 1 := by
  classical
  let Q := (I ×ˢ J).filter fun u ↦ b * startCompleteVertexLabel y L u.1 = a * startCompleteVertexLabel z L u.2
  have hQ : Q ⊆ units a b y z L \ D := by
    intro u hu
    obtain ⟨huIJ, hunit⟩ := mem_filter.mp hu
    refine mem_sdiff.mpr ⟨mem_units.mpr hunit, ?_⟩
    intro huD
    exact (havoid u huD).elim (fun h ↦ h (mem_product.mp huIJ).1) (fun h ↦ h (mem_product.mp huIJ).2)
  have hsub : dilate b (I.image (startCompleteVertexLabel y L)) ∩
      dilate a (J.image (startCompleteVertexLabel z L)) ⊆
      Q.image (fun u ↦ b * startCompleteVertexLabel y L u.1) := by
    intro n hn
    obtain ⟨nl, hnl, hnlEq⟩ := mem_image.mp (mem_inter.mp hn).1
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hnl
    obtain ⟨nr, hnr, hnrEq⟩ := mem_image.mp (mem_inter.mp hn).2
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hnr
    exact mem_image.mpr ⟨(i, j), mem_filter.mpr ⟨mem_product.mpr ⟨hi, hj⟩, hnlEq.trans hnrEq.symm⟩, hnlEq⟩
  exact (card_le_card hsub).trans (card_image_le.trans ((card_le_card hQ).trans hremaining))

end PaperP1.TwoTargetUnitExclusion
