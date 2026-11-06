module

public import PaperP1.Analysis.DirichletGramLargeValues
public import PaperP1.Analysis.LogarithmicSquareRootBound

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SquareRootGramBound
open Finset PaperP1 LogarithmicPhase GaussianExponentialSums FiniteGramLargeValues
open scoped Classical

def cap (N : ℕ) (Δ T : ℝ) : ℝ :=
  Real.sqrt (128*((N : ℝ)*Real.sqrt (2*T)+(N : ℝ)^2/Real.sqrt Δ)*(1+Real.log (N : ℝ)))

theorem cap_nonneg (N : ℕ) (Δ T : ℝ) : 0 ≤ cap N Δ T := Real.sqrt_nonneg _

theorem actual_sum_bound (N : ℕ) (hN : 0 < N) (t Δ T : ℝ) (hΔ : 1 ≤ Δ) (hT : 1 ≤ T)
    (hlow : Δ ≤ |t|) (hupp : |t| ≤ 2*T) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖ ≤ cap N Δ T := by
  have hΔpos : 0 < Δ := by linarith
  have hsΔ : 0 < Real.sqrt Δ := Real.sqrt_pos.2 hΔpos
  have hslow := Real.sqrt_le_sqrt hlow
  have hsupp := Real.sqrt_le_sqrt hupp
  have hlogN := Real.log_natCast_nonneg N
  have hbase : 0 ≤ 128*((N : ℝ)*Real.sqrt (2*T)+(N : ℝ)^2/Real.sqrt Δ)*(1+Real.log (N : ℝ)) := by positivity
  have hh := LogarithmicSquareRootBound.square_bound N hN t (hΔ.trans hlow)
  have hm : (N : ℝ)*Real.sqrt |t|+(N : ℝ)^2/Real.sqrt |t| ≤
      (N : ℝ)*Real.sqrt (2*T)+(N : ℝ)^2/Real.sqrt Δ :=
    add_le_add (mul_le_mul_of_nonneg_left hsupp (Nat.cast_nonneg N))
      (div_le_div_of_nonneg_left (sq_nonneg _) hsΔ hslow)
  have hp := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 128)) (by linarith : 0 ≤ 1+Real.log (N : ℝ)))
  have he : (cap N Δ T)^2=128*((N : ℝ)*Real.sqrt (2*T)+(N : ℝ)^2/Real.sqrt Δ)*(1+Real.log (N : ℝ)) := Real.sq_sqrt hbase
  nlinarith [norm_nonneg (∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n),cap_nonneg N Δ T]

theorem mixed_sum_bound (N : ℕ) (hN : 0 < N) (t T : ℝ) (ht : 1 ≤ |t|) (hT : 1 ≤ T)
    (hupp : |t| ≤ 2*T) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖ ≤
      min (3*(N : ℝ)/|t|+|t|) (cap N |t| T) := by
  exact le_min (LogarithmicExponentialSum.exponential_sum_bound N hN t (abs_pos.mp (by linarith)))
    (actual_sum_bound N hN t |t| T ht hT le_rfl hupp)

theorem separated_correlation_cap {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T Δ : ℝ) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Δ ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (r : ι) (hr : r ∈ R) (s : ι) (hs : s ∈ R) (hne : r ≠ s) :
    ‖gram (Ico N (2*N)) (fun r n ↦ phase (-Real.log n) (τ r)) r s‖ ≤ cap N Δ T := by
  rw [DirichletGramLargeValues.gram_identity]
  apply actual_sum_bound N hN (τ r-τ s) Δ T hΔ hT (hsep r hr s hs hne)
  apply abs_le.mpr
  constructor <;> linarith [(htau r hr).1,(htau r hr).2,(htau s hs).1,(htau s hs).2]

theorem analysis_bound {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T Δ : ℝ) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Δ ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) :
    (∑ r ∈ R, ‖polynomial (Ico N (2*N)) a (fun n ↦ -Real.log n) (τ r)‖^2) ≤
      ((N : ℝ)+(R.card : ℝ)*cap N Δ T)*(∑ n ∈ Ico N (2*N), ‖a n‖^2) := by
  apply montgomery_analysis_bound (Ico N (2*N)) R a (fun r n ↦ phase (-Real.log n) (τ r))
    (N : ℝ) (cap N Δ T) (Nat.cast_nonneg _) (cap_nonneg N Δ T)
  · intro r hr
    have he := DirichletGramLargeValues.diagonal_norm (Ico N (2*N)) τ r
    have hc : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
    rw [hc] at he
    exact he.le
  · exact fun r hr s hs hne ↦ separated_correlation_cap R τ T Δ hT hΔ htau hsep N hN r hr s hs hne

theorem large_values_card {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T Δ : ℝ) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Δ ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V)
    (hbig : ∀ r ∈ R, V ≤ ‖polynomial (Ico N (2*N)) a (fun n ↦ -Real.log n) (τ r)‖)
    (hden : 0 < V^2-cap N Δ T*(∑ n ∈ Ico N (2*N), ‖a n‖^2)) :
    (R.card : ℝ) ≤ (N : ℝ)*(∑ n ∈ Ico N (2*N), ‖a n‖^2)/
      (V^2-cap N Δ T*(∑ n ∈ Ico N (2*N), ‖a n‖^2)) := by
  apply montgomery_large_values_card (Ico N (2*N)) R a (fun r n ↦ phase (-Real.log n) (τ r))
    (N : ℝ) (cap N Δ T) (Nat.cast_nonneg _) (cap_nonneg N Δ T)
  · intro r hr
    have he := DirichletGramLargeValues.diagonal_norm (Ico N (2*N)) τ r
    have hc : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
    rw [hc] at he
    exact he.le
  · exact fun r hr s hs hne ↦ separated_correlation_cap R τ T Δ hT hΔ htau hsep N hN r hr s hs hne
  · exact hV
  · exact hbig
  · exact hden
end PaperP1.SquareRootGramBound
