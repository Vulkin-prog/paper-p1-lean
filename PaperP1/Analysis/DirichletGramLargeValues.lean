module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.FiniteGramLargeValues

/-! # Actual logarithmic Gram correlations and explicit separated large-value bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirichletGramLargeValues
open Finset PaperP1 LogarithmicPhase GaussianExponentialSums FiniteGramLargeValues
open scoped Classical

theorem phase_time_difference (w t s : ℝ) : phase w t*star (phase w s)=phase w (t-s) := by
  rw [phase_conj,phase,phase,phase,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem gram_identity {ι : Type*} (S : Finset ℕ) (τ : ι → ℝ) (r s : ι) :
    gram S (fun r n ↦ phase (-Real.log n) (τ r)) r s =
      ∑ n ∈ S, LogarithmicExponentialSum.function (τ r-τ s) n := by
  apply sum_congr rfl
  intro n hn
  exact phase_time_difference (-Real.log n) (τ r) (τ s)

theorem diagonal_norm {ι : Type*} (S : Finset ℕ) (τ : ι → ℝ) (r : ι) :
    ‖gram S (fun r n ↦ phase (-Real.log n) (τ r)) r r‖=(S.card : ℝ) := by
  rw [gram_identity]
  simp [LogarithmicExponentialSum.function,phase]

theorem dyadic_correlation {ι : Type*} (N : ℕ) (hN : 0 < N) (τ : ι → ℝ) (r s : ι)
    (hne : τ r-τ s ≠ 0) :
    ‖gram (Ico N (2*N)) (fun r n ↦ phase (-Real.log n) (τ r)) r s‖ ≤
      3*(N : ℝ)/|τ r-τ s|+|τ r-τ s| := by
  rw [gram_identity]
  exact LogarithmicExponentialSum.exponential_sum_bound N hN (τ r-τ s) hne

theorem separated_correlation_cap {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T Δ : ℝ) (hΔ : 0 < Δ) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Δ ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (r : ι) (hr : r ∈ R) (s : ι) (hs : s ∈ R) (hne : r ≠ s) :
    ‖gram (Ico N (2*N)) (fun r n ↦ phase (-Real.log n) (τ r)) r s‖ ≤
      3*(N : ℝ)/Δ+2*T := by
  have hlow := hsep r hr s hs hne
  have hpos : 0 < |τ r-τ s| := hΔ.trans_le hlow
  have hupp : |τ r-τ s| ≤ 2*T := by
    apply abs_le.mpr
    constructor <;> linarith [(htau r hr).1,(htau r hr).2,(htau s hs).1,(htau s hs).2]
  exact (dyadic_correlation N hN τ r s (abs_pos.mp hpos)).trans
    (add_le_add (div_le_div_of_nonneg_left (by positivity) hΔ hlow) hupp)

theorem large_values_card {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → Δ ≤ |τ r-τ s|)
    (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V)
    (hbig : ∀ r ∈ R, V ≤ ‖polynomial (Ico N (2*N)) a (fun n ↦ -Real.log n) (τ r)‖)
    (hden : 0 < V^2-(3*(N : ℝ)/Δ+2*T)*(∑ n ∈ Ico N (2*N), ‖a n‖^2)) :
    (R.card : ℝ) ≤
      (N : ℝ)*(∑ n ∈ Ico N (2*N), ‖a n‖^2)/
        (V^2-(3*(N : ℝ)/Δ+2*T)*(∑ n ∈ Ico N (2*N), ‖a n‖^2)) := by
  apply montgomery_large_values_card (Ico N (2*N)) R a (fun r n ↦ phase (-Real.log n) (τ r))
    (N : ℝ) (3*(N : ℝ)/Δ+2*T) (Nat.cast_nonneg N) (by positivity)
  · intro r hr
    have he := diagonal_norm (Ico N (2*N)) τ r
    have hc : (Ico N (2*N)).card=N := by rw [Nat.card_Ico]; omega
    rw [hc] at he
    exact he.le
  · exact fun r hr s hs hne ↦ separated_correlation_cap R τ T Δ hΔ htau hsep N hN r hr s hs hne
  · exact hV
  · exact hbig
  · exact hden
end DirichletGramLargeValues
