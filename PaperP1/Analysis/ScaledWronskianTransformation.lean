module

public import PaperP1.Analysis.ScaledDerivativeExpansion
public import PaperP1.Analysis.AnalyticWronskianProduct

/-! # Exact Wronskian transformation for an actual scaled differential chain

The derivative expansion matrix is lower triangular. Its diagonal product is
an exact power of the scale, so nonzero scales preserve nonzero determinants.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledWronskianTransformation

open Set Finset ScaledDerivativeExpansion AnalyticWronskianProduct
open scoped ContDiff

def transformation (n : ℕ) (a : ℝ → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ coefficient a i.val j.val t

def chainMatrix (n : ℕ) (F : Fin n → ℕ → ℝ → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ F j i.val t

theorem transformation_lower (n : ℕ) (a : ℝ → ℝ) (t : ℝ) :
    (transformation n a t).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  change coefficient a i.val j.val t = 0
  rw [coefficient_above a i.val j.val (by exact hij)]

theorem transformation_det (n : ℕ) (a : ℝ → ℝ) (t : ℝ) :
    (transformation n a t).det = (a t) ^ (∑ i : Fin n, i.val) := by
  rw [Matrix.det_of_isLowerTriangular _ (transformation_lower n a t)]
  simp only [transformation, coefficient_diagonal]
  exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Fin n ↦ i.val) (a t)

theorem transformation_det_ne_zero (n : ℕ) (a : ℝ → ℝ) (t : ℝ) (ha : a t ≠ 0) :
    (transformation n a t).det ≠ 0 := by
  rw [transformation_det]
  exact pow_ne_zero _ ha

theorem jetMatrix_expansion (n : ℕ) (a : ℝ → ℝ) (F : Fin n → ℕ → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s)
    (hF : ∀ j k, ∀ t ∈ s, HasDerivAt (F j k) (a t * F j (k + 1) t) t)
    (t : ℝ) (ht : t ∈ s) :
    jetMatrix n (fun j ↦ F j 0) t = transformation n a t * chainMatrix n F t := by
  ext i j
  rw [Matrix.mul_apply]
  change iteratedDeriv i.val (F j 0) t =
    ∑ k : Fin n, coefficient a i.val k.val t * F j k.val t
  rw [iterated_expansion a (F j) s hs ha (hF j) i.val ht]
  calc
    _ = ∑ k : Fin n, if k.val ≤ i.val then coefficient a i.val k.val t * F j k.val t else 0 :=
      (sum_initial n i.val i.isLt (fun k ↦ coefficient a i.val k t * F j k t)).symm
    _ = _ := by
      apply sum_congr rfl
      intro k _hk
      by_cases hk : k.val ≤ i.val
      · rw [ite_eq_left hk]
      · rw [ite_eq_right hk, coefficient_above a i.val k.val (by omega), zero_mul]

theorem wronskian_factor (n : ℕ) (a : ℝ → ℝ) (F : Fin n → ℕ → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s)
    (hF : ∀ j k, ∀ t ∈ s, HasDerivAt (F j k) (a t * F j (k + 1) t) t)
    (t : ℝ) (ht : t ∈ s) :
    wronskian n (fun j ↦ F j 0) t =
      (a t) ^ (∑ i : Fin n, i.val) * (chainMatrix n F t).det := by
  change (jetMatrix n (fun j ↦ F j 0) t).det = _
  rw [jetMatrix_expansion n a F s hs ha hF t ht, Matrix.det_mul, transformation_det]

theorem wronskian_ne_zero (n : ℕ) (a : ℝ → ℝ) (F : Fin n → ℕ → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s)
    (hF : ∀ j k, ∀ t ∈ s, HasDerivAt (F j k) (a t * F j (k + 1) t) t)
    (t : ℝ) (ht : t ∈ s) (hscale : a t ≠ 0) (hdet : (chainMatrix n F t).det ≠ 0) :
    wronskian n (fun j ↦ F j 0) t ≠ 0 := by
  rw [wronskian_factor n a F s hs ha hF t ht]
  exact mul_ne_zero (pow_ne_zero _ hscale) hdet

end PaperP1.ScaledWronskianTransformation
