module

public import PaperP1.Analysis.DirichletPolynomialMeanValue

/-! # Actual support cardinality controls coefficient squares and Dirichlet mean values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SupportedCoefficientSquareBudget
open Finset PaperP1 DirichletPolynomialMeanValue
open scoped Classical

def constant : ℝ := Real.exp 1*(Real.sqrt Real.pi+4*Real.pi)

theorem constant_pos : 0 < constant := by unfold constant; positivity

theorem term_bound (N n : ℕ) (hN : 0 < N) (hNn : N ≤ n) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z/(n : ℂ)‖^2 ≤ 1/(N : ℝ)^2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hnpos : (0 : ℝ) < n := hNr.trans_le hnr
  have hh : ‖z/(n : ℂ)‖ ≤ 1/(N : ℝ) := by
    rw [norm_div,Complex.norm_natCast]
    exact (div_le_div_of_nonneg_right hz hnpos.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hNr hnr)
  have hp := pow_le_pow_left₀ (norm_nonneg _) hh 2
  simpa only [div_pow,one_pow] using hp

theorem support_square_budget (N : ℕ) (hN : 0 < N) (S E : Finset ℕ)
    (hS : S ⊆ Ico N (2*N)) (hES : E ⊆ S) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (hzero : ∀ n ∈ S, n ∉ E → a n=0) :
    (∑ n ∈ S, ‖a n/(n : ℂ)‖^2) ≤ (E.card : ℝ)/(N : ℝ)^2 := by
  have he : (∑ n ∈ E, ‖a n/(n : ℂ)‖^2) = ∑ n ∈ S, ‖a n/(n : ℂ)‖^2 := by
    apply sum_subset hES
    intro n hn hnE
    rw [hzero n hn hnE]
    simp
  rw [← he]
  calc
    _ ≤ ∑ _n ∈ E, 1/(N : ℝ)^2 := sum_le_sum (fun n hn ↦
      term_bound N n hN (mem_Ico.mp (hS (hES hn))).1 (a n) (ha n (hES hn)))
    _ = _ := by simp [div_eq_mul_inv]

theorem supported_mean_square (N : ℕ) (hN : 0 < N) (S E : Finset ℕ)
    (hS : S ⊆ Ico N (2*N)) (hES : E ⊆ S) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (hzero : ∀ n ∈ S, n ∉ E → a n=0)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖value S a t‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*T+4*Real.pi*(N : ℝ))*((E.card : ℝ)/(N : ℝ)^2) := by
  exact (dyadic_mean_square N hN S hS a T hT).trans
    (mul_le_mul_of_nonneg_left (support_square_budget N hN S E hS hES a ha hzero) (by positivity))

theorem supported_uniform_bound (N : ℕ) (hN : 0 < N) (S E : Finset ℕ)
    (hS : S ⊆ Ico N (2*N)) (hES : E ⊆ S) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) (hzero : ∀ n ∈ S, n ∉ E → a n=0)
    (T : ℝ) (hT : 0 < T) (hTN : T ≤ N) :
    (∫ t in -T..T, ‖value S a t‖^2) ≤ constant*((E.card : ℝ)/(N : ℝ)) := by
  have hh := supported_mean_square N hN S E hS hES a ha hzero T hT
  have hc : Real.exp 1*(Real.sqrt Real.pi*T+4*Real.pi*(N : ℝ)) ≤ constant*(N : ℝ) := by
    unfold constant
    have hm := mul_le_mul_of_nonneg_left hTN (Real.sqrt_nonneg Real.pi)
    have he := mul_le_mul_of_nonneg_left
      (add_le_add hm (le_rfl : 4*Real.pi*(N : ℝ) ≤ 4*Real.pi*(N : ℝ))) (Real.exp_pos 1).le
    nlinarith
  have hb := hh.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  calc
    _ ≤ constant*(N : ℝ)*((E.card : ℝ)/(N : ℝ)^2) := hb
    _ = _ := by field_simp
end SupportedCoefficientSquareBudget
