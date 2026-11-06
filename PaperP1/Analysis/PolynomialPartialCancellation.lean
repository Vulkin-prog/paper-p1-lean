module

public import PaperP1.Analysis.IteratedLogarithmicSum
public import PaperP1.Analysis.PolynomialLogarithmicCancellation
public import PaperP1.Analysis.PartialLogarithmicPower

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PolynomialPartialCancellation
open Finset PaperP1 PolynomialLogarithmicCancellation
open scoped Classical

theorem elementary_bound (X L : ℕ) (hX : 0 < X) (hLX : L ≤ X) (t : ℝ) (ht : t ≠ 0) :
    ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖ ≤ 4*(X : ℝ)/|t|+|t| := by
  have hh := IteratedLogarithmicSum.integer_sum_bound [] (by simp) X (X+L) hX (by omega) t ht
  simp only [IteratedLogarithmicPhase.function_nil,List.sum_nil,List.length_nil,List.prod_nil,
    Nat.factorial_zero,Nat.cast_one,zero_add,pow_one,add_zero,mul_one,Nat.add_sub_cancel_left] at hh
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hLXR : (L : ℝ) ≤ X := by exact_mod_cast hLX
  have hNum : 2*((X+L : ℕ) : ℝ) ≤ 4*(X : ℝ) := by push_cast; linarith only [hLXR]
  have hFirst := div_le_div_of_nonneg_right hNum (abs_nonneg t)
  have hSecond := mul_le_mul_of_nonneg_right hLXR (div_nonneg (abs_nonneg t) hXR.le)
  have he : (X : ℝ)*(|t|/(X : ℝ))=|t| := by field_simp
  rw [he] at hSecond
  linarith only [hh,hFirst,hSecond]

theorem uniform_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ L ≤ X, ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖ ≤ constant b*(X : ℝ)^(1-decay a b) := by
  obtain ⟨X₀,hX₀,hHigh⟩ := PartialLogarithmicPower.uniform_bound (order b) (order_pos b)
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper L hLX
  have hX1 : 1 ≤ X := by omega
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have ht : 0 < |t| := (Real.rpow_pos_of_pos hXp a).trans_le hLower
  obtain ⟨hDa,hDQuarter,hDHigh⟩ := decay_bounds a b
  have hTargetNN := Real.rpow_nonneg (Nat.cast_nonneg X) (1-decay a b)
  by_cases hCase : (X : ℝ)^(3/4 : ℝ) ≤ |t|
  · have hB : b ≤ (order b : ℝ)+1/4 := by linarith only [order_real b]
    have hUpper' := hUpper.trans (Real.rpow_le_rpow_of_exponent_le hXR hB)
    have hBound := hHigh X hX t hCase hUpper' L hLX
    change ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖ ≤
      ActualLogarithmicPower.constant (order b)*(X : ℝ)^(1-ActualLogarithmicPower.decay (order b)) at hBound
    have hPower := Real.rpow_le_rpow_of_exponent_le hXR
      (show 1-ActualLogarithmicPower.decay (order b) ≤ 1-decay a b by linarith only [hDHigh])
    have hC := ActualLogarithmicPower.constant_four_le (order b)
    have hCNN : 0 ≤ ActualLogarithmicPower.constant (order b) := by linarith only [hC]
    calc
      _ ≤ ActualLogarithmicPower.constant (order b)*(X : ℝ)^(1-decay a b) :=
        hBound.trans (mul_le_mul_of_nonneg_left hPower hCNN)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold constant; linarith) hTargetNN
  · have hElem := elementary_bound X L (by omega) hLX t (abs_pos.mp ht)
    have hFirstDen : 4*(X : ℝ)/|t| ≤ 4*(X : ℝ)/(X : ℝ)^a :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hXp a) hLower
    have hPowerA := Real.rpow_le_rpow_of_exponent_le hXR
      (show 1-a ≤ 1-decay a b by linarith only [hDa])
    have hRatio : (X : ℝ)/(X : ℝ)^a=(X : ℝ)^(1-a) := by rw [Real.rpow_sub hXp,Real.rpow_one]
    have hFirst : 4*(X : ℝ)/(X : ℝ)^a ≤ 4*(X : ℝ)^(1-decay a b) := by
      calc
        _ = 4*((X : ℝ)/(X : ℝ)^a) := by ring
        _ = 4*(X : ℝ)^(1-a) := by rw [hRatio]
        _ ≤ _ := mul_le_mul_of_nonneg_left hPowerA (by norm_num)
    have hSecond : |t| ≤ (X : ℝ)^(1-decay a b) :=
      (lt_of_not_ge hCase).le.trans (Real.rpow_le_rpow_of_exponent_le hXR (by linarith only [hDQuarter]))
    have hTotal : ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖ ≤ 5*(X : ℝ)^(1-decay a b) := by
      linarith only [hElem,hFirstDen,hFirst,hSecond]
    exact hTotal.trans (mul_le_mul_of_nonneg_right (show 5 ≤ constant b by
      unfold PolynomialLogarithmicCancellation.constant
      have hh := ActualLogarithmicPower.constant_four_le (order b)
      linarith only [hh]) hTargetNN)

theorem relative_bound (a b : ℝ) :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ L ≤ X, ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖/(X : ℝ) ≤ constant b/(X : ℝ)^(decay a b) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound a b
  refine ⟨X₀,hX₀,?_⟩
  intro X hX t hLower hUpper L hLX
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  calc
    _ ≤ (constant b*(X : ℝ)^(1-decay a b))/(X : ℝ) :=
      div_le_div_of_nonneg_right (hBound X hX t hLower hUpper L hLX) (Nat.cast_nonneg X)
    _ = _ := by
      rw [Real.rpow_sub hXp,Real.rpow_one]
      field_simp [hXp.ne',(Real.rpow_pos_of_pos hXp (decay a b)).ne']

theorem power_gain (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ t : ℝ,
      (X : ℝ)^a ≤ |t| → |t| ≤ (X : ℝ)^b →
      ∀ L ≤ X, ‖∑ j ∈ Ico X (X+L), LogarithmicExponentialSum.function t j‖ ≤ C*(X : ℝ)^(1-c) := by
  obtain ⟨X₀,hX₀,hBound⟩ := uniform_bound a b
  exact ⟨constant b,by linarith only [constant_four_le b],decay a b,decay_pos a b ha,X₀,hX₀,hBound⟩
end PaperP1.PolynomialPartialCancellation
