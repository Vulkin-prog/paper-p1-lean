module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Separate target component and singleton budgets for a monochromatic physical partition -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TargetComponentBudget

open Finset

variable {V A : Type*} [DecidableEq V] [DecidableEq A] [Zero A]

def labels (ℓ : V → A) (T : Finset V) : Finset A := (T.image ℓ).erase 0

def meeting (C : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  C.filter fun D ↦ (D ∩ T).Nonempty

def singleton (C : Finset (Finset V)) (T : Finset V) : Finset (Finset V) :=
  C.filter fun D ↦ (D ∩ T).card = 1

theorem labels_le_components (ℓ : V → A) (C : Finset (Finset V)) (T : Finset V)
    (hcover : ∀ v ∈ T, ℓ v ≠ 0 → ∃ D ∈ C, v ∈ D)
    (hmono : ∀ D ∈ C, ∀ v ∈ D, ∀ w ∈ D, ℓ v = ℓ w) :
    (labels ℓ T).card ≤ (meeting C T).card := by
  have hsub : labels ℓ T ⊆ (meeting C T).biUnion fun D ↦ labels ℓ D := by
    intro a ha
    obtain ⟨ha0, haT⟩ := mem_erase.mp ha
    obtain ⟨v, hvT, hv⟩ := mem_image.mp haT
    obtain ⟨D, hDC, hvD⟩ := hcover v hvT (by rwa [hv])
    exact mem_biUnion.mpr ⟨D, mem_filter.mpr ⟨hDC, ⟨v, mem_inter.mpr ⟨hvD, hvT⟩⟩⟩,
      mem_erase.mpr ⟨ha0, mem_image.mpr ⟨v, hvD, hv⟩⟩⟩
  have hcard : ∀ D ∈ meeting C T, (labels ℓ D).card ≤ 1 := by
    intro D hD
    apply (card_erase_le).trans
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ha
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hb
    exact hmono D (mem_filter.mp hD).1 v hv w hw
  calc
    _ ≤ ((meeting C T).biUnion fun D ↦ labels ℓ D).card := card_le_card hsub
    _ ≤ ∑ D ∈ meeting C T, (labels ℓ D).card := card_biUnion_le
    _ ≤ ∑ _D ∈ meeting C T, 1 := sum_le_sum hcard
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

omit [DecidableEq A] [Zero A] in
theorem intersections_card_le (C : Finset (Finset V)) (T : Finset V)
    (hdisj : (C : Set (Finset V)).Pairwise Disjoint) :
    (∑ D ∈ C, (D ∩ T).card) ≤ T.card := by
  have hpair : (C : Set (Finset V)).Pairwise (fun D E ↦ Disjoint (D ∩ T) (E ∩ T)) := by
    intro D hD E hE hDE
    exact (hdisj hD hE hDE).mono inter_subset_left inter_subset_left
  rw [← card_biUnion hpair]
  apply card_le_card
  intro v hv
  obtain ⟨D, _hD, hvD⟩ := mem_biUnion.mp hv
  exact (mem_inter.mp hvD).2

omit [DecidableEq A] [Zero A] in
theorem singleton_budget (C : Finset (Finset V)) (T : Finset V)
    (hdisj : (C : Set (Finset V)).Pairwise Disjoint) :
    2 * (meeting C T).card ≤ T.card + (singleton C T).card := by
  have hsum := intersections_card_le C T hdisj
  have hpoint : ∀ D ∈ C, 2 * (if (D ∩ T).Nonempty then 1 else 0) ≤
      (D ∩ T).card + (if (D ∩ T).card = 1 then 1 else 0) := by
    intro D _hD
    by_cases hne : (D ∩ T).Nonempty
    · have hp := hne.card_pos
      by_cases hone : (D ∩ T).card = 1
      · simp only [hne, hone, ite_true]; omega
      · simp only [hne, hone, ite_true, ite_false, add_zero]
        omega
    · have hzero : (D ∩ T).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hne)
      simp only [hne, hzero, ite_false, zero_ne_one, add_zero, mul_zero]
      exact le_refl 0
  have hbound := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] at hbound
  change 2 * (meeting C T).card ≤ _ at hbound
  change _ ≤ T.card + (C.filter fun D ↦ (D ∩ T).card = 1).card
  omega

omit [DecidableEq A] [Zero A] in
theorem singleton_lower (C : Finset (Finset V)) (T : Finset V)
    (hdisj : (C : Set (Finset V)).Pairwise Disjoint) :
    2 * (meeting C T).card - T.card ≤ (singleton C T).card := by
  have h := singleton_budget C T hdisj
  omega

end PaperP1.TargetComponentBudget
