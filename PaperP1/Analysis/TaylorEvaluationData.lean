module

public import PaperP1.Analysis.ActualTaylorRemainderBound
public import PaperP1.Algebra.RealFilteredEvaluationDeterminant
public import Mathlib.Data.Fintype.Sum

/-! # Actual Taylor-plus-remainder data for a real evaluation matrix

There is one slot for each low Taylor degree and one remainder slot for each
function. The slot indices are distinct; all remainder weights are capped.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TaylorEvaluationData

open Set Finset ActualTaylorRemainderBound WeightedEvaluationDeterminant
open scoped ContDiff

def slotIndex (n : ℕ) : Fin (n - 1) ⊕ Fin n → ℕ :=
  Sum.elim (fun k ↦ k.val) (fun k ↦ n - 1 + k.val)

def coefficients {n : ℕ} (f : Fin n → ℝ → ℝ) (c M : ℝ) (i : Fin n) :
    Fin (n - 1) ⊕ Fin n → ℝ
  | Sum.inl k => iteratedDeriv k.val (f i) c / (k.val.factorial : ℝ)
  | Sum.inr k => if i = k then M else 0

def values {n : ℕ} (f : Fin n → ℝ → ℝ) (c M : ℝ) (x : Fin n → ℝ) :
    (Fin (n - 1) ⊕ Fin n) → Fin n → ℝ
  | Sum.inl k, j => (x j - c) ^ k.val
  | Sum.inr k, j => (f k (x j) - jet (f k) (n - 2) c (x j)) / M

theorem slotIndex_injective (n : ℕ) : Function.Injective (slotIndex n) := by
  intro x y h
  cases x with
  | inl k =>
    cases y with
    | inl l =>
      congr 1
      apply Fin.ext
      exact h
    | inr l =>
      change k.val = n - 1 + l.val at h
      have hk := k.isLt
      omega
  | inr k =>
    cases y with
    | inl l =>
      change n - 1 + k.val = l.val at h
      have hl := l.isLt
      omega
    | inr l =>
      congr 1
      apply Fin.ext
      change n - 1 + k.val = n - 1 + l.val at h
      omega

theorem evaluation_eq (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ → ℝ)
    (c M : ℝ) (hM : M ≠ 0) (x : Fin n → ℝ) :
    evaluationMatrix (coefficients f c M) (values f c M x) = (fun i j ↦ f i (x j)) := by
  ext i j
  change (∑ s : Fin (n - 1) ⊕ Fin n, coefficients f c M i s * values f c M x s j) = f i (x j)
  have hL : (∑ k : Fin (n - 1), coefficients f c M i (Sum.inl k) * values f c M x (Sum.inl k) j) =
      jet (f i) (n - 2) c (x j) := by
    change (∑ k : Fin (n - 1), iteratedDeriv k.val (f i) c / (k.val.factorial : ℝ) * (x j - c) ^ k.val) = _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ iteratedDeriv k (f i) c / (k.factorial : ℝ) * (x j - c) ^ k) (n - 1), jet,
      show n - 2 + 1 = n - 1 by omega]
    apply sum_congr rfl
    intro k _hk
    ring
  have hH : (∑ k : Fin n, coefficients f c M i (Sum.inr k) * values f c M x (Sum.inr k) j) =
      f i (x j) - jet (f i) (n - 2) c (x j) := by
    change (∑ k : Fin n, (if i = k then M else 0) *
      ((f k (x j) - jet (f k) (n - 2) c (x j)) / M)) = _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    field_simp [hM]
  rw [Fintype.sum_sum_type, hL, hH]
  ring

theorem coefficient_bound (n : ℕ) (f : Fin n → ℝ → ℝ) (c M : ℝ) (hM : 1 ≤ M)
    (hD : ∀ i k, k ≤ n - 1 → |iteratedDeriv k (f i) c| ≤ M) :
    ∀ i s, |coefficients f c M i s| ≤ M := by
  have hM₀ : 0 ≤ M := zero_le_one.trans hM
  intro i s
  cases s with
  | inl k =>
    exact factorial_divisor_bound _ M k.val (hD i k.val (by have := k.isLt; omega))
  | inr k =>
    change |if i = k then M else 0| ≤ M
    split_ifs
    · exact (abs_of_nonneg hM₀).le
    · simpa only [abs_zero] using hM₀

theorem value_bound (n : ℕ) (hn : 2 ≤ n) (f : Fin n → ℝ → ℝ) (a b : ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b))
    (c M δ : ℝ) (hc : c ∈ Ioo a b) (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (x : Fin n → ℝ) (hx : ∀ j, x j ∈ Ioo a b) (hdist : ∀ j, |x j - c| ≤ δ)
    (hD : ∀ i y, y ∈ Ioo a b → |iteratedDeriv (n - 1) (f i) y| ≤ M) :
    ∀ s j, |values f c M x s j| ≤ δ ^ min (slotIndex n s) (n - 1) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  intro s j
  cases s with
  | inl k =>
    change |(x j - c) ^ k.val| ≤ δ ^ min k.val (n - 1)
    rw [min_eq_left (show k.val ≤ n - 1 by have := k.isLt; omega), abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hdist j) _
  | inr k =>
    change |(f k (x j) - jet (f k) (n - 2) c (x j)) / M| ≤ δ ^ min (n - 1 + k.val) (n - 1)
    rw [min_eq_right (show n - 1 ≤ n - 1 + k.val by omega), abs_div, abs_of_pos hMpos]
    apply (div_le_iff₀ hMpos).mpr
    have hr := remainder_bound (f k) a b (hf k) (n - 2) c (x j) hc (hx j) M δ hMpos.le hδ (hdist j)
      (fun y hy ↦ by simpa only [show n - 2 + 1 = n - 1 by omega] using hD k y hy)
    simpa only [show n - 2 + 1 = n - 1 by omega, mul_comm] using hr

end PaperP1.TaylorEvaluationData
