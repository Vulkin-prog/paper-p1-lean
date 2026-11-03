module

public import PaperP1.Model.SecondOrderRetainedReference

/-! # Finite positive boundary mass for the all-pair class, with the entire one-pair term subtracted -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondOrderPositiveMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ActualComponentRemainder PaperP1.SecondOrderRetainedClass PaperP1.SecondOrderRetainedReference

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem pointwise_bound (G : Finset ℕ) (L K : ℕ) (η u : ℝ) (hu : 0 ≤ u)
    (I : Finset ℕ) (hIG : I ⊆ G) (hsize : I.card ≤ K) (hcap : (runRelativeNullity L I : ℝ) ≤ η * L) :
    u ^ I.card * infiniteJointMoment L I ≤ u ^ I.card * |coefficient L I| +
      ∑ D ∈ NonretainedPositiveMass.residual G L K η (G.powersetCard 2),
        if D ⊆ I then weight L u D * ∏ x ∈ I \ D, u * infiniteMarginal x L else 0 := by
  classical
  let T := insert ∅ (I.powersetCard 2)
  let A := I.powerset \ T
  let f := fun D ↦ infiniteCenteredCoefficient L D * ∏ x ∈ I \ D, infiniteMarginal x L
  have hsub : T ⊆ I.powerset := by
    intro D hD
    rcases mem_insert.mp hD with rfl | hD
    · exact empty_mem_powerset I
    · exact mem_powerset.mpr (mem_powersetCard.mp hD).1
  have hlow : (∑ D ∈ T, f D) = coefficient L I := by
    have he : (∅ : Finset ℕ) ∉ I.powersetCard 2 := by simp
    simp only [T, f, sum_insert he, CompressedJointMoments.centered_empty, sdiff_empty, one_mul]
    rfl
  have hsplit := sum_sdiff hsub (f := f)
  rw [hlow, ← CompressedJointMoments.infinite_uncentered_expansion L I] at hsplit
  have hrem : (∑ D ∈ A, u ^ I.card * f D) ≤
      ∑ D ∈ NonretainedPositiveMass.residual G L K η (G.powersetCard 2),
        if D ⊆ I then weight L u D * ∏ x ∈ I \ D, u * infiniteMarginal x L else 0 := by
    let R := NonretainedPositiveMass.residual G L K η (G.powersetCard 2)
    have hsubR : A ⊆ R := by
      intro D hD
      obtain ⟨hDI, hnot⟩ := mem_sdiff.mp hD
      have hDIs := mem_powerset.mp hDI
      have hne : D.Nonempty := nonempty_iff_ne_empty.mpr (fun hz ↦ hnot (mem_insert.mpr (Or.inl hz)))
      have hnotpair : D ∉ G.powersetCard 2 := by
        intro hpair
        exact hnot (mem_insert.mpr (Or.inr (mem_powersetCard.mpr ⟨hDIs, (mem_powersetCard.mp hpair).2⟩)))
      have hmono : (runRelativeNullity L D : ℝ) ≤ runRelativeNullity L I := by
        exact_mod_cast relativeNullityOn_mono (fun x ↦ squareClassSpace x L) hDIs
      exact (NonretainedPositiveMass.mem_residual G D L K η _).mpr
        ⟨hDIs.trans hIG, hne, (card_le_card hDIs).trans hsize, hmono.trans hcap, hnotpair⟩
    calc
      _ ≤ ∑ D ∈ A, if D ⊆ I then weight L u D * ∏ x ∈ I \ D, u * infiniteMarginal x L else 0 := by
        apply sum_le_sum
        intro D hD
        have hDI := mem_powerset.mp (mem_sdiff.mp hD).1
        rw [ite_eq_left hDI]
        dsimp only [f, weight]
        rw [← NonretainedPositiveMass.weighted_term L I D hDI u _]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _)
          (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)) (pow_nonneg hu _)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsubR (fun D _ _ ↦ by
        split_ifs
        · exact mul_nonneg (mul_nonneg (pow_nonneg hu _) (abs_nonneg _))
            (prod_nonneg fun x _ ↦ mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
        · exact le_rfl)
  have hcoef := mul_le_mul_of_nonneg_left (le_abs_self (coefficient L I)) (pow_nonneg hu I.card)
  have hscaled := congrArg (fun a : ℝ ↦ u ^ I.card * a) hsplit
  rw [mul_add, mul_sum] at hscaled
  change (∑ D ∈ A, u ^ I.card * f D) + u ^ I.card * coefficient L I = u ^ I.card * infiniteJointMoment L I at hscaled
  linarith only [hrem, hcoef, hscaled]

theorem finite_bound (G : Finset ℕ) (L K : ℕ) (hL : 0 < L) (η u : ℝ) (hu : 0 ≤ u)
    (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ K ∧ (runRelativeNullity L I : ℝ) ≤ η * L ∧ ¬Retained G L I) :
    (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤
      Real.exp (∑ x ∈ G, u * infiniteMarginal x L) * (∑ D ∈ SecondOrderIndependentDeficit.primitives G L, weight L u D) +
      2 * u ^ 2 * AllPairExtensionDeficit.deficit G L u +
      Real.exp (∑ x ∈ G, u * infiniteMarginal x L) *
        (Real.exp ((∑ e ∈ G.powersetCard 2, weight L u e) + ∑ C ∈ higher G L K η, weight L u C) -
          1 - ∑ e ∈ G.powersetCard 2, weight L u e) := by
  let R := NonretainedPositiveMass.residual G L K η (G.powersetCard 2)
  have hground : ∀ I ∈ F, I ⊆ G ∧ ¬Retained G L I := fun I hI ↦ ⟨(hF I hI).1, (hF I hI).2.2.2.2⟩
  have hcoeff := sum_le_sum fun I hI ↦ weighted_coefficient G L I (hF I hI).1 u hu
  simp only [sum_add_distrib] at hcoeff
  have hind := SecondOrderIndependentDeficit.independent_bound G L hL u hu F hground
  have hp := SecondOrderIndependentDeficit.pair_bound G L u hu F hground
  have hrem := SeedComplementSum.finite_bound G F R (fun x ↦ u * infiniteMarginal x L) (weight L u)
    (fun x ↦ mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
    (fun D _ ↦ mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) (fun I hI ↦ (hF I hI).1)
    (fun D hD ↦ ((NonretainedPositiveMass.mem_residual G D L K η _).mp hD).1)
  have hcomponents := ActualComponentRemainder.finite_bound G L K hL η u hu (G.powersetCard 2) R Subset.rfl
    (fun D hD ↦ (NonretainedPositiveMass.mem_residual G D L K η _).mp hD)
  have hrem2 := hrem.trans (mul_le_mul_of_nonneg_left hcomponents (Real.exp_nonneg _))
  have hpoint := sum_le_sum fun I hI ↦ pointwise_bound G L K η u hu I (hF I hI).1 (hF I hI).2.2.1 (hF I hI).2.2.2.1
  simp only [sum_add_distrib] at hpoint
  linarith only [hcoeff, hind, hp, hrem2, hpoint]

end PaperP1.SecondOrderPositiveMass
