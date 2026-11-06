module

public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Analysis.ReciprocalSquareTail
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ReciprocalFrequencyWeights
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def inverseSquare (n : ℕ) : ℝ := 1/((n+1 : ℕ) : ℝ)^2

theorem inverseSquare_finite_bound (S : Finset ℕ) : (∑ n ∈ S, inverseSquare n) ≤ 2 := by
  have hh := ReciprocalSquareTail.finite_bound 1 (by norm_num) (S.image (fun n ↦ n+1)) (by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
    exact_mod_cast (by omega : 1 ≤ n+1))
  rw [sum_image (by intro n hn m hm he; change n+1=m+1 at he; omega)] at hh
  norm_num only [div_one] at hh
  exact hh

theorem inverseSquare_summable : Summable inverseSquare :=
  summable_of_sum_le (fun n ↦ by dsimp only [inverseSquare]; positivity) inverseSquare_finite_bound

theorem inverseSquare_tsum_bound : (∑' n : ℕ, inverseSquare n) ≤ 2 :=
  Real.tsum_le_of_sum_le (fun n ↦ by dsimp only [inverseSquare]; positivity) inverseSquare_finite_bound

theorem finite_weight_bound (S : Finset ℕ) (K : ℕ) :
    (∑ j ∈ S, 1/(1+((j : ℝ)-(K : ℝ))^2)) ≤ 5 := by
  have hh := GaussianFrequencyRowBound.translated_sequence_bound S K
    (fun j ↦ 1/(1+((j : ℝ)-(K : ℝ))^2)) inverseSquare inverseSquare_summable
    (fun n ↦ by dsimp only [inverseSquare]; positivity) (by simp) (by
      intro j hj hji
      change 1/(1+((j : ℝ)-(K : ℝ))^2) ≤ 1/((K-j-1+1 : ℕ) : ℝ)^2
      rw [show K-j-1+1=K-j by omega,Nat.cast_sub hji.le]
      apply one_div_le_one_div_of_le (sq_pos_of_pos (sub_pos.mpr (by exact_mod_cast hji)))
      nlinarith) (by
      intro j hj hKj
      change 1/(1+((j : ℝ)-(K : ℝ))^2) ≤ 1/((j-K-1+1 : ℕ) : ℝ)^2
      rw [show j-K-1+1=j-K by omega,Nat.cast_sub hKj.le]
      apply one_div_le_one_div_of_le (sq_pos_of_pos (sub_pos.mpr (by exact_mod_cast hKj)))
      linarith)
  linarith [inverseSquare_tsum_bound]

theorem local_sup_bound (F : ℝ → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t : ℝ, ‖F t‖ ≤ M) (h : ℝ) :
    PrimeUnitMean.localSquareSup F h ≤ M^2 := by
  obtain ⟨t,ht,he⟩ := PrimeUnitMean.local_sup_attained F hF h
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM t) 2

theorem frequency_budget_bound (F : ℝ → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t : ℝ, ‖F t‖ ≤ M) (K : ℕ) :
    PrimeUnitMean.frequencyBudget F K ≤ 5*M^2 := by
  calc
    _ ≤ ∑ j ∈ range (2*K+1), M^2/(1+((j : ℝ)-(K : ℝ))^2) := by
      apply sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_right (local_sup_bound F hF M hM _) (by positivity)
    _ = M^2*(∑ j ∈ range (2*K+1), 1/(1+((j : ℝ)-(K : ℝ))^2)) := by rw [mul_sum]; apply sum_congr rfl; intro j hj; ring
    _ ≤ _ := by have hh := mul_le_mul_of_nonneg_left (finite_weight_bound (range (2*K+1)) K) (sq_nonneg M); nlinarith
end PaperP1.ReciprocalFrequencyWeights
