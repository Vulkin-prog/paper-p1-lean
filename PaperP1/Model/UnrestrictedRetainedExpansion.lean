module

public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.UnrestrictedRunComponents
public import PaperP1.Model.PrimitiveActiveSeeds
public import PaperP1.Model.ActualCanonicalComponents

/-! # Exact pair expansion on every retained family, including zero marginals and incompatible pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnrestrictedRetainedExpansion

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem centered_zero_of_no_full_support (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hno : ¬ ∃ w, IsFullSupportRelation (fun i : I ↦ squareClassSpace i.val L) w) :
    infiniteCenteredCoefficient L I = 0 := by
  by_cases hp : ∀ x ∈ I, 0 < infiniteMarginal x L
  · exact CompressedJointMoments.centered_zero_of_no_full_support L hL I hp hno
  · push Not at hp
    obtain ⟨x, hx, hpx⟩ := hp
    exact PositiveMarginalRestriction.zero_centered L I x hx (le_antisymm hpx
      (MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem centered_zero_direct (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hne : I.Nonempty)
    (hz : runRelativeNullity L I = 0) : infiniteCenteredCoefficient L I = 0 :=
  centered_zero_of_no_full_support L hL I
    (CompressedRelationSupport.no_full_support_of_nullity_zero (fun x ↦ squareClassSpace x L) I hne hz)

theorem centered_zero_retained_large (L : ℕ) (hL : 0 < L) (E : Finset (Finset ℕ))
    (hE : ∀ e ∈ E, e.card = 2) (I : Finset ℕ)
    (hI : RetainedDependence.Retained (fun x ↦ squareClassSpace x L) E I) (hlarge : 3 ≤ I.card) :
    infiniteCenteredCoefficient L I = 0 :=
  centered_zero_of_no_full_support L hL I
    (CompressedRelationSupport.no_full_support_retained_large (fun x ↦ squareClassSpace x L) E hE I hI hlarge)

theorem joint_pair_expansion (L : ℕ) (hL : 0 < L) (E : Finset (Finset ℕ))
    (hE : ∀ e ∈ E, e.card = 2) (I : Finset ℕ)
    (hI : RetainedDependence.Retained (fun x ↦ squareClassSpace x L) E I) :
    infiniteJointMoment L I = (∏ x ∈ I, infiniteMarginal x L) +
      ∑ e ∈ I.powersetCard 2, infiniteCenteredCoefficient L e * ∏ x ∈ I \ e, infiniteMarginal x L := by
  classical
  let T := insert ∅ (I.powersetCard 2)
  have hsub : T ⊆ I.powerset := by
    intro A hA
    rcases mem_insert.mp hA with rfl | hA
    · exact empty_mem_powerset I
    · exact mem_powerset.mpr (mem_powersetCard.mp hA).1
  have hsum : (∑ A ∈ T, infiniteCenteredCoefficient L A * ∏ x ∈ I \ A, infiniteMarginal x L) =
      ∑ A ∈ I.powerset, infiniteCenteredCoefficient L A * ∏ x ∈ I \ A, infiniteMarginal x L := by
    apply sum_subset hsub
    intro A hA hnot
    have hne : A.Nonempty := nonempty_iff_ne_empty.mpr (fun hz ↦ hnot (mem_insert.mpr (Or.inl hz)))
    have hcard : A.card ≠ 2 := fun hc ↦ hnot (mem_insert.mpr (Or.inr (mem_powersetCard.mpr ⟨mem_powerset.mp hA, hc⟩)))
    have hzero : infiniteCenteredCoefficient L A = 0 := by
      by_cases hone : A.card = 1
      · obtain ⟨x, rfl⟩ := card_eq_one.mp hone
        exact ActualCanonicalComponents.singleton_zero L x
      · exact centered_zero_retained_large L hL E hE A
          (RetainedDependence.hereditary (fun x ↦ squareClassSpace x L) E hE
            (mem_powerset.mp hA) hI) (by have h := hne.card_pos; omega)
    rw [hzero, zero_mul]
  rw [CompressedJointMoments.infinite_uncentered_expansion, ← hsum]
  have he : (∅ : Finset ℕ) ∉ I.powersetCard 2 := by simp
  simp only [T, sum_insert he, CompressedJointMoments.centered_empty, sdiff_empty, one_mul]

theorem primitive_centered (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hI : ConnectedWindowFamilies.Primitive L I) :
    infiniteCenteredCoefficient L I = infiniteJointMoment L I - ∏ x ∈ I, infiniteMarginal x L := by
  classical
  have hne : I.Nonempty := card_pos.mp (lt_of_lt_of_le (by norm_num : 0 < 2)
    (PrimitiveActiveSeeds.primitive_card_ge_two L I hI))
  let f := fun A ↦ infiniteCenteredCoefficient L A * ∏ x ∈ I \ A, infiniteMarginal x L
  have hsub : ({∅, I} : Finset (Finset ℕ)) ⊆ I.powerset := by
    intro A hA
    rcases mem_insert.mp hA with rfl | hA
    · exact empty_mem_powerset I
    · exact mem_powerset.mpr ((mem_singleton.mp hA) ▸ Subset.rfl)
  have hsum : (∑ A ∈ ({∅, I} : Finset (Finset ℕ)), f A) = ∑ A ∈ I.powerset, f A := by
    apply sum_subset hsub
    intro A hA hnot
    have hAn : A.Nonempty := nonempty_iff_ne_empty.mpr (fun hz ↦ hnot (by simp [hz]))
    have hAI : A ⊂ I := Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hA, fun hz ↦ hnot (by simp [hz])⟩
    dsimp only [f]
    rw [centered_zero_direct L hL A hAn (hI.2 A hAI), zero_mul]
  have hq := CompressedJointMoments.infinite_uncentered_expansion L I
  change infiniteJointMoment L I = ∑ A ∈ I.powerset, f A at hq
  rw [← hsum, sum_pair (Ne.symm hne.ne_empty)] at hq
  simp only [f, CompressedJointMoments.centered_empty, sdiff_empty, one_mul, sdiff_self, bot_eq_empty, prod_empty, mul_one] at hq
  linarith only [hq]

theorem primitive_independent_le (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hI : ConnectedWindowFamilies.Primitive L I) :
    (∏ x ∈ I, infiniteMarginal x L) ≤ |infiniteCenteredCoefficient L I| := by
  have hP : 0 ≤ ∏ x ∈ I, infiniteMarginal x L :=
    prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  rw [primitive_centered L hL I hI]
  by_cases hq : 0 < infiniteJointMoment L I
  · have hformula := infiniteJointMoment_exact_of_pos (I.sup fun x ↦ x + L) L I hL
      (fun x hx ↦ le_sup (f := fun x ↦ x + L) hx) hq
    have hp : (2 : ℝ) ≤ 2 ^ runRelativeNullity L I := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ runRelativeNullity L I from hI.1)
      simpa only [pow_one] using h
    have hbound := mul_le_mul_of_nonneg_left hp hP
    change infiniteJointMoment L I = (∏ x ∈ I, infiniteMarginal x L) * (2 ^ runRelativeNullity L I : ℝ) at hformula
    have hsign : 0 ≤ infiniteJointMoment L I - ∏ x ∈ I, infiniteMarginal x L := by nlinarith only [hbound, hformula, hP]
    rw [abs_of_nonneg hsign]
    nlinarith only [hbound, hformula]
  · have hz : infiniteJointMoment L I = 0 := le_antisymm (le_of_not_gt hq) (infiniteJointMoment_nonneg L I)
    rw [hz, zero_sub, abs_neg, abs_of_nonneg hP]

end PaperP1.UnrestrictedRetainedExpansion
