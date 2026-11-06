module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.ActualLogarithmicPower

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PolynomialLogarithmicCancellation
open Finset PaperP1
open scoped Classical

def order (b : ℝ) : ℕ := max 1 ⌈b⌉₊

def decay (a b : ℝ) : ℝ := min a (min (1/4) (ActualLogarithmicPower.decay (order b)))

def constant (b : ℝ) : ℝ := ActualLogarithmicPower.constant (order b)+5

theorem order_pos (b : ℝ) : 0 < order b := by unfold order; omega

theorem order_real (b : ℝ) : b ≤ (order b : ℝ) := by
  have hh : ⌈b⌉₊ ≤ order b := le_max_right 1 ⌈b⌉₊
  exact (Nat.le_ceil b).trans (by exact_mod_cast hh)

theorem decay_pos (a b : ℝ) (ha : 0 < a) : 0 < decay a b := by
  unfold decay
  exact lt_min ha (lt_min (by norm_num) (ActualLogarithmicPower.decay_pos (order b) (order_pos b)))

theorem decay_bounds (a b : ℝ) :
    decay a b ≤ a ∧ decay a b ≤ 1/4 ∧ decay a b ≤ ActualLogarithmicPower.decay (order b) := by
  exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩

theorem constant_four_le (b : ℝ) : 4 ≤ constant b := by
  have hh := ActualLogarithmicPower.constant_four_le (order b)
  unfold constant
  linarith only [hh]

theorem uniform_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤ constant b*(X : ℝ)^(1-decay a b) := by
  obtain ⟨X₀,hX₀,hHigh⟩ := ActualLogarithmicPower.uniform_bound (order b) (order_pos b)
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper
  have hX1 : 1 ≤ X := by omega
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have ht : 0 < |t| := (Real.rpow_pos_of_pos hXp a).trans_le hLower
  obtain ⟨hDa,hDQuarter,hDHigh⟩ := decay_bounds a b
  have hTargetNN := Real.rpow_nonneg (Nat.cast_nonneg X) (1-decay a b)
  by_cases hCase : (X : ℝ)^(3/4 : ℝ) ≤ |t|
  · have hB : b ≤ (order b : ℝ)+1/4 := by linarith only [order_real b]
    have hUpper' := hUpper.trans (Real.rpow_le_rpow_of_exponent_le hXR hB)
    have hBound := hHigh X hX t hCase hUpper'
    have hPower := Real.rpow_le_rpow_of_exponent_le hXR
      (show 1-ActualLogarithmicPower.decay (order b) ≤ 1-decay a b by linarith only [hDHigh])
    have hC := ActualLogarithmicPower.constant_four_le (order b)
    have hCNN : 0 ≤ ActualLogarithmicPower.constant (order b) := by linarith only [hC]
    calc
      _ ≤ ActualLogarithmicPower.constant (order b)*(X : ℝ)^(1-decay a b) :=
        hBound.trans (mul_le_mul_of_nonneg_left hPower hCNN)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold constant; linarith) hTargetNN
  · have hElem := LogarithmicExponentialSum.exponential_sum_bound X (by omega) t (abs_pos.mp ht)
    have hFirstDen : 3*(X : ℝ)/|t| ≤ 3*(X : ℝ)/(X : ℝ)^a :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hXp a) hLower
    have hPowerA := Real.rpow_le_rpow_of_exponent_le hXR
      (show 1-a ≤ 1-decay a b by linarith only [hDa])
    have hRatio : (X : ℝ)/(X : ℝ)^a=(X : ℝ)^(1-a) := by rw [Real.rpow_sub hXp,Real.rpow_one]
    have hFirst : 3*(X : ℝ)/(X : ℝ)^a ≤ 3*(X : ℝ)^(1-decay a b) := by
      calc
        _ = 3*((X : ℝ)/(X : ℝ)^a) := by ring
        _ = 3*(X : ℝ)^(1-a) := by rw [hRatio]
        _ ≤ _ := mul_le_mul_of_nonneg_left hPowerA (by norm_num)
    have hSecond : |t| ≤ (X : ℝ)^(1-decay a b) :=
      (lt_of_not_ge hCase).le.trans (Real.rpow_le_rpow_of_exponent_le hXR (by linarith only [hDQuarter]))
    have hTotal : ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤ 4*(X : ℝ)^(1-decay a b) := by
      linarith only [hElem,hFirstDen,hFirst,hSecond]
    exact hTotal.trans (mul_le_mul_of_nonneg_right (constant_four_le b) hTargetNN)

theorem relative_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖/(X : ℝ) ≤ constant b/(X : ℝ)^(decay a b) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound a b
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  calc
    _ ≤ (constant b*(X : ℝ)^(1-decay a b))/(X : ℝ) :=
      div_le_div_of_nonneg_right (hBound X hX t hLower hUpper) (Nat.cast_nonneg X)
    _ = _ := by
      rw [Real.rpow_sub hXp,Real.rpow_one]
      field_simp [hXp.ne',(Real.rpow_pos_of_pos hXp (decay a b)).ne']

theorem power_gain (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ‖∑ j ∈ Ico X (2*X), LogarithmicExponentialSum.function t j‖ ≤ C*(X : ℝ)^(1-c) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound a b
  exact ⟨constant b,by linarith only [constant_four_le b],decay a b,decay_pos a b ha,X₀,hX₀,hBound⟩
end PaperP1.PolynomialLogarithmicCancellation
