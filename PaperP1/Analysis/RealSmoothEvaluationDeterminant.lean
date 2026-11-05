module

public import PaperP1.Analysis.TaylorEvaluationData

/-! # An actual short-interval real smooth evaluation determinant bound

Only actual derivatives and actual evaluation points are hypotheses. The
Taylor/remainder representation and capped-weight determinant power are proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealSmoothEvaluationDeterminant

open Set TaylorEvaluationData
open scoped ContDiff

theorem bound (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ → ℝ) (a b c : ℝ) (hc : c ∈ Ioo a b)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b)) (M δ : ℝ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Ioo a b) (hdist : ∀ j, |x j - c| ≤ δ)
    (hD : ∀ i k, k ≤ n - 1 → ∀ y ∈ Ioo a b, |iteratedDeriv k (f i) y| ≤ M) :
    |Matrix.det (fun i j : Fin n ↦ f i (x j))| ≤
      ((((n - 1) + n : ℕ) : ℝ)) ^ n * M ^ n * (n.factorial : ℝ) * δ ^ (n * (n - 1) / 2) := by
  have hne : M ≠ 0 := (zero_lt_one.trans_le hM).ne'
  have hh := RealFilteredEvaluationDeterminant.weighted_bound n (slotIndex n) (slotIndex_injective n)
    (coefficients f c M) (values f c M x) M δ (zero_le_one.trans hM) hδ hδone
    (coefficient_bound n f c M hM (fun i k hk ↦ hD i k hk c hc))
    (value_bound n hn f a b hf c M δ hc hM hδ x hx hdist (fun i y hy ↦ hD i (n - 1) le_rfl y hy))
  rw [evaluation_eq n hn f c M hne x] at hh
  simpa only [Fintype.card_sum, Fintype.card_fin] using hh

theorem coarse_bound (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ → ℝ) (a b c : ℝ) (hc : c ∈ Ioo a b)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b)) (M δ : ℝ)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Ioo a b) (hdist : ∀ j, |x j - c| ≤ δ)
    (hD : ∀ i k, k ≤ n - 1 → ∀ y ∈ Ioo a b, |iteratedDeriv k (f i) y| ≤ M) :
    |Matrix.det (fun i j : Fin n ↦ f i (x j))| ≤
      (((2 * n : ℕ) : ℝ)) ^ n * M ^ n * (n.factorial : ℝ) * δ ^ (n * (n - 1) / 2) := by
  have hcard : ((((n - 1) + n : ℕ) : ℝ)) ≤ (((2 * n : ℕ) : ℝ)) := by
    exact_mod_cast (show n - 1 + n ≤ 2 * n by omega)
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ (((n - 1) + n : ℕ) : ℝ) from Nat.cast_nonneg _) hcard n
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  exact (bound n hn f a b c hc hf M δ hM hδ hδone x hx hdist hD).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (pow_nonneg hM₀ n)) (Nat.cast_nonneg _))
      (pow_nonneg hδ _))

end PaperP1.RealSmoothEvaluationDeterminant
