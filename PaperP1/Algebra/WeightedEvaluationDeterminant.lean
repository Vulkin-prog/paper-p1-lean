module

public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.GCongr
public import Mathlib.Basic.Real.Basic

/-! # Polynomial evaluation determinants use distinct monomial rows only -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedEvaluationDeterminant

open Finset

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [CommRing R]

def evaluationMatrix (C : ι → κ → R) (V : κ → ι → R) : Matrix ι ι R :=
  Matrix.of fun i j ↦ ∑ k, C i k * V k j

def selectedMatrix (V : κ → ι → R) (f : ι → κ) : Matrix ι ι R :=
  Matrix.of fun i j ↦ V (f i) j

theorem determinant_expansion (C : ι → κ → R) (V : κ → ι → R) :
    (evaluationMatrix C V).det = ∑ f : ι → κ, (∏ i, C i (f i)) * (selectedMatrix V f).det := by
  have hm : evaluationMatrix C V = fun i ↦ ∑ k, C i k • V k := by
    ext i j
    simp only [evaluationMatrix, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hm]
  change Matrix.detRowAlternating.toMultilinearMap (fun i ↦ ∑ k, C i k • V k) = _
  rw [MultilinearMap.map_sum]
  apply sum_congr rfl
  intro f _
  rw [MultilinearMap.map_smul_univ]
  rfl

omit [Fintype κ] in
theorem selected_zero_of_not_injective (V : κ → ι → R) (f : ι → κ)
    (hf : ¬ Function.Injective f) : (selectedMatrix V f).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_row_eq hne
  exact congrArg V hij

theorem determinant_injective_expansion [DecidableEq κ] (C : ι → κ → R) (V : κ → ι → R) :
    (evaluationMatrix C V).det =
      ∑ f ∈ (univ : Finset (ι → κ)).filter Function.Injective,
        (∏ i, C i (f i)) * (selectedMatrix V f).det := by
  rw [determinant_expansion]
  apply (sum_subset (filter_subset _ _) ?_).symm
  intro f _ hf
  have hn : ¬ Function.Injective f := by simpa only [mem_filter, mem_univ, true_and] using hf
  rw [selected_zero_of_not_injective V f hn, mul_zero]

theorem row_weight_bound (M : Matrix ι ι ℝ) (W : ι → ℝ)
    (hM : ∀ i j, |M i j| ≤ W i) :
    |M.det| ≤ (Fintype.card ι).factorial * ∏ i, W i := by
  let abv : AbsoluteValue ℝ ℝ := AbsoluteValue.abs
  calc
    |M.det| = abv (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, M (σ i) i) := by rw [Matrix.det_apply]; rfl
    _ ≤ ∑ σ : Equiv.Perm ι, abv (Equiv.Perm.sign σ • ∏ i, M (σ i) i) := abv.sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |M (σ i) i| := by
      apply sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, W (σ i) := by
      apply sum_le_sum
      intro σ _
      gcongr with i
      exact hM (σ i) i
    _ = ∑ _σ : Equiv.Perm ι, ∏ i, W i := by
      apply sum_congr rfl
      intro σ _
      exact Equiv.prod_comp σ W
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem weighted_bound (C : ι → κ → ℝ) (V : κ → ι → ℝ) (W : κ → ℝ) (K T : ℝ)
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hC : ∀ i k, |C i k| ≤ K) (hV : ∀ k j, |V k j| ≤ W k)
    (hprod : ∀ f : ι → κ, Function.Injective f → (∏ i, W (f i)) ≤ T) :
    |(evaluationMatrix C V).det| ≤
      (Fintype.card κ : ℝ) ^ Fintype.card ι * K ^ Fintype.card ι *
        (Fintype.card ι).factorial * T := by
  rw [determinant_expansion]
  calc
    |∑ f : ι → κ, (∏ i, C i (f i)) * (selectedMatrix V f).det| ≤
        ∑ f : ι → κ, |(∏ i, C i (f i)) * (selectedMatrix V f).det| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f : ι → κ, K ^ Fintype.card ι * (Fintype.card ι).factorial * T := by
      apply sum_le_sum
      intro f _
      by_cases hf : Function.Injective f
      · have hc : |∏ i, C i (f i)| ≤ K ^ Fintype.card ι := by
          rw [Finset.abs_prod]
          calc
            _ ≤ ∏ _i : ι, K := by
              gcongr with i
              exact hC i (f i)
            _ = _ := by simp only [prod_const, card_univ]
        have hv := (row_weight_bound (selectedMatrix V f) (fun i ↦ W (f i))
          (fun i j ↦ hV (f i) j)).trans
            (mul_le_mul_of_nonneg_left (hprod f hf) (Nat.cast_nonneg _))
        rw [abs_mul]
        simpa only [mul_assoc] using mul_le_mul hc hv (abs_nonneg _) (pow_nonneg hK _)
      · rw [selected_zero_of_not_injective V f hf, mul_zero, abs_zero]
        positivity
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fun, nsmul_eq_mul, Nat.cast_pow]
      ring

end PaperP1.WeightedEvaluationDeterminant
