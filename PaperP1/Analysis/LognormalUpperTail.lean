module

public import PaperP1.Analysis.LognormalSieveWeight
public import PaperP1.Analysis.ClippedPowerSum
public import PaperP1.Analysis.LognormalSumIntegrability

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalUpperTail
open Finset Filter PaperP1 LognormalSieveWeight
open scoped Classical

def tail (A t : ℝ) (M : ℕ) : ℂ :=
  ∑' k : ℕ, (weight A ((k+M : ℕ) : ℝ) : ℂ)*LogarithmicExponentialSum.function t ((k+M : ℕ) : ℝ)

theorem reciprocal_cube_tail (S : Finset ℕ) (M : ℕ) (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n) :
    (∑ n ∈ S, 1/(n : ℝ)^3) ≤ 8/(M : ℝ)^2 := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hh := ClippedPowerSum.finite_tail_le_power S 3 ((M : ℝ)/2) (by norm_num) (by linarith)
    (fun n hn ↦ by
      have hh : (M : ℝ) ≤ n := by exact_mod_cast hS n hn
      linarith only [hh,hMR])
  convert hh using 1
  · apply sum_congr rfl
    intro n hn
    norm_num [Real.rpow_neg,Real.rpow_ofNat,div_eq_mul_inv]
  · norm_num [PowerSeriesTail.constant,Real.rpow_neg,Real.rpow_two,div_pow,mul_pow,mul_inv_rev,inv_div,div_eq_mul_inv]
    ring

theorem finite_norm_bound (A t : ℝ) (hA : 0 < A) (S : Finset ℕ) (M : ℕ)
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n) :
    ‖∑ n ∈ S, (weight A n : ℂ)*LogarithmicExponentialSum.function t n‖ ≤
      8*Real.exp 1*A^3/(M : ℝ)^2 := by
  calc
    _ ≤ ∑ n ∈ S, ‖(weight A n : ℂ)*LogarithmicExponentialSum.function t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, (Real.exp 1*A^3)*(1/(n : ℝ)^3) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos A n),LogarithmicExponentialSum.function_norm,mul_one]
      exact (polynomial_tail_bound A n hA (by exact_mod_cast (show 0 < n by have hh := hS n hn; omega))).trans_eq (by ring)
    _ = (Real.exp 1*A^3)*(∑ n ∈ S, 1/(n : ℝ)^3) := by rw [mul_sum]
    _ ≤ (Real.exp 1*A^3)*(8/(M : ℝ)^2) := mul_le_mul_of_nonneg_left (reciprocal_cube_tail S M hM hS) (by positivity)
    _ = _ := by ring

theorem summable_terms (A t : ℝ) (hA : 0 < A) (M : ℕ) (hM : 1 ≤ M) :
    Summable (fun k : ℕ ↦ (weight A ((k+M : ℕ) : ℝ) : ℂ)*
      LogarithmicExponentialSum.function t ((k+M : ℕ) : ℝ)) := by
  have hh := (summable_nat_add_iff (M-1)).mpr (LognormalSumIntegrability.summable_terms A t hA)
  apply hh.congr
  intro k
  rw [show (k+(M-1))+1=k+M by omega]

theorem norm_bound (A t : ℝ) (hA : 0 < A) (M : ℕ) (hM : 2 ≤ M) :
    ‖tail A t M‖ ≤ 8*Real.exp 1*A^3/(M : ℝ)^2 := by
  have hSum := summable_terms A t hA M (by omega)
  apply le_of_tendsto hSum.hasSum.tendsto_sum_nat.norm
  apply Filter.Eventually.of_forall
  intro L
  have hInj : Set.InjOn (fun k : ℕ ↦ k+M) (range L) := by
    intro i hi j hj he
    change i+M=j+M at he
    omega
  have hh := finite_norm_bound A t hA ((range L).image (fun k ↦ k+M)) M hM (by
    intro n hn
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hn
    omega)
  rw [sum_image hInj] at hh
  exact hh

theorem square_cutoff_bound (A t : ℝ) (hA : 2 ≤ A) :
    ‖tail A t ⌈A^2⌉₊‖ ≤ 8*Real.exp 1/A := by
  have hAP : 0 < A := by linarith only [hA]
  have hCut : 2 ≤ ⌈A^2⌉₊ := by
    have hh := Nat.le_ceil (A^2)
    have hp : (2 : ℝ) ≤ ⌈A^2⌉₊ := by nlinarith only [hh,hA]
    exact_mod_cast hp
  have hPower := pow_le_pow_left₀ (sq_nonneg A) (Nat.le_ceil (A^2)) 2
  calc
    _ ≤ 8*Real.exp 1*A^3/(⌈A^2⌉₊ : ℝ)^2 := norm_bound A t hAP _ hCut
    _ ≤ 8*Real.exp 1*A^3/(A^2)^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hPower
    _ = _ := by field_simp [hAP.ne']
end PaperP1.LognormalUpperTail
