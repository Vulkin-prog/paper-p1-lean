module

public import PaperP1.Analysis.GaussianExponentialSums
public import PaperP1.Analysis.GaussianFrequencyRowBound

/-! # An unconditional universal mean-value bound for the literal finite Dirichlet polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirichletPolynomialMeanValue
open PaperP1 Finset MeasureTheory GaussianExponentialSums GaussianFrequencyRowBound
open scoped Classical

theorem separated_interval_bound (S : Finset ℕ) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, δ * |(j : ℝ)-(i : ℝ)| ≤ |w j-w i|) :
    (∫ t in -T..T, ‖polynomial S a w t‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi * T + 2*Real.pi/δ) * ∑ i ∈ S, ‖a i‖^2 := by
  let b := 1/T^2
  have hb : 0 < b := by dsimp only [b]; positivity
  let L := 1 + Real.sqrt (Real.pi/(δ^2/(4*b)))
  have hrow : ∀ i ∈ S, (∑ j ∈ S, Real.exp (-((w i-w j)^2/(4*b)))) ≤ L := by
    intro i hi
    exact separated_row_bound S w i b δ hb hδ (hgap i hi)
  have hlocal := interval_le_gaussian S a w b T hb hT
  have hglobal := gaussian_mean_square_le S a w b L hb hrow
  have hbT : b*T^2 = 1 := by dsimp only [b]; field_simp
  rw [hbT] at hlocal
  have hroot1 : Real.sqrt (Real.pi/b) = Real.sqrt Real.pi * T := by
    dsimp only [b]
    have he : Real.pi / (1/T^2) = Real.pi*T^2 := by field_simp
    rw [he, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hT.le]
  have hroot2 : Real.sqrt (Real.pi/(δ^2/(4*b))) = Real.sqrt Real.pi * (2/(δ*T)) := by
    have he : Real.pi/(δ^2/(4*b)) = Real.pi*(2/(δ*T))^2 := by
      dsimp only [b]
      field_simp
      ring
    rw [he, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (by positivity : 0 ≤ 2/(δ*T))]
  have hroots : Real.sqrt (Real.pi/b)*L = Real.sqrt Real.pi*T + 2*Real.pi/δ := by
    dsimp only [L]
    rw [hroot1, hroot2]
    calc
      _ = Real.sqrt Real.pi*T + 2*(Real.sqrt Real.pi)^2/δ := by field_simp
      _ = _ := by rw [Real.sq_sqrt Real.pi_pos.le]
  have hh := mul_le_mul_of_nonneg_left hglobal (Real.exp_pos 1).le
  rw [hroots] at hh
  simpa only [mul_assoc] using hlocal.trans hh
theorem logarithmic_interval_bound (S : Finset ℕ) (a : ℕ → ℂ) (M : ℕ) (hM : 0 < M)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ M) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖polynomial S a (fun n ↦ -Real.log n) t‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*T + 2*Real.pi*(M : ℝ)) * ∑ i ∈ S, ‖a i‖^2 := by
  have hh := separated_interval_bound S a (fun n ↦ -Real.log n) T (1/(M : ℝ)) hT (by positivity) (by
    intro i hi j hj
    have hg := integer_log_gap M i j (hS i hi).1 (hS j hj).1 (hS i hi).2 (hS j hj).2
    simpa only [neg_sub_neg, abs_sub_comm] using hg)
  have he : 2*Real.pi/(1/(M : ℝ)) = 2*Real.pi*(M : ℝ) := by field_simp
  simpa only [he] using hh

def value (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  polynomial S (fun n ↦ a n / (n : ℂ)) (fun n ↦ -Real.log n) t

theorem dyadic_mean_square (N : ℕ) (hN : 0 < N) (S : Finset ℕ) (hS : S ⊆ Ico N (2*N))
    (a : ℕ → ℂ) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖value S a t‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*T + 4*Real.pi*(N : ℝ)) *
        ∑ n ∈ S, ‖a n / (n : ℂ)‖^2 := by
  have hh := logarithmic_interval_bound S (fun n ↦ a n/(n : ℂ)) (2*N) (by omega) (by
    intro n hn
    have hm := mem_Ico.mp (hS hn)
    omega) T hT
  have he : 2*Real.pi*((2*N : ℕ) : ℝ) = 4*Real.pi*(N : ℝ) := by push_cast; ring
  simpa only [value, he] using hh

theorem unit_coefficient_square_budget (N : ℕ) (hN : 0 < N) (S : Finset ℕ)
    (hS : S ⊆ Ico N (2*N)) (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) :
    (∑ n ∈ S, ‖a n / (n : ℂ)‖^2) ≤ 1/(N : ℝ) := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcard : S.card ≤ N := by
    have hh := card_le_card hS
    rw [Nat.card_Ico] at hh
    omega
  have hpoint : ∀ n ∈ S, ‖a n / (n : ℂ)‖ ≤ 1/(N : ℝ) := by
    intro n hn
    have hnN : N ≤ n := (mem_Ico.mp (hS hn)).1
    rw [norm_div, RCLike.norm_natCast]
    calc
      _ ≤ 1/(n : ℝ) := div_le_div_of_nonneg_right (ha n hn) (Nat.cast_nonneg n)
      _ ≤ _ := div_le_div_of_nonneg_left zero_le_one hnR (by exact_mod_cast hnN)
  calc
    _ ≤ ∑ _n ∈ S, (1/(N : ℝ))^2 := by
      apply sum_le_sum
      intro n hn
      have hh := hpoint n hn
      nlinarith [norm_nonneg (a n/(n : ℂ))]
    _ = (S.card : ℝ)*(1/(N : ℝ))^2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ)*(1/(N : ℝ))^2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
    _ = _ := by field_simp

theorem bounded_dyadic_mean_square (N : ℕ) (hN : 0 < N) (S : Finset ℕ)
    (hS : S ⊆ Ico N (2*N)) (a : ℕ → ℂ) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖value S a t‖^2) ≤
      Real.exp 1 * (Real.sqrt Real.pi*(T/(N : ℝ)) + 4*Real.pi) := by
  have hh := dyadic_mean_square N hN S hS a T hT
  have hc := unit_coefficient_square_budget N hN S hS a ha
  calc
    _ ≤ Real.exp 1 * (Real.sqrt Real.pi*T + 4*Real.pi*(N : ℝ)) *
        (1/(N : ℝ)) := hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = _ := by field_simp

theorem uniform_mean_value :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ S : Finset ℕ, S ⊆ Ico N (2*N) →
      ∀ a : ℕ → ℂ, (∀ n ∈ S, ‖a n‖ ≤ 1) → ∀ T : ℝ, 0 < T →
        (∫ t in -T..T, ‖value S a t‖^2) ≤ C * (T/(N : ℝ) + 1) := by
  let C := Real.exp 1 * (Real.sqrt Real.pi + 4*Real.pi)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro N hN S hS a ha T hT
  have hh := bounded_dyadic_mean_square N hN S hS a ha T hT
  have hx : 0 ≤ T/(N : ℝ) := by positivity
  have hscalar : Real.sqrt Real.pi*(T/(N : ℝ)) + 4*Real.pi ≤
      (Real.sqrt Real.pi + 4*Real.pi)*(T/(N : ℝ)+1) := by
    nlinarith [Real.sqrt_nonneg Real.pi, mul_nonneg Real.pi_pos.le hx]
  exact hh.trans (by simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left hscalar (Real.exp_pos 1).le)

end DirichletPolynomialMeanValue
