module

public import Mathlib.Analysis.PSeries
public import PaperP1.Analysis.LogarithmicExponentialSum
public import PaperP1.Analysis.DampedLogarithmicIntegral
public import PaperP1.Analysis.DampedLogarithmicQuadrature

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DampedDirichletTail
open Finset Filter MeasureTheory PaperP1 DampedLogarithmicIntegral
open scoped Classical

def series (σ t : ℝ) : ℂ := ∑' n : ℕ, integrand σ t n

def tail (σ t : ℝ) (N : ℕ) : ℂ := ∑' k : ℕ, integrand σ t ((k+N : ℕ) : ℝ)

theorem term_norm (σ t : ℝ) (hσ : 0 ≤ σ) (n : ℕ) :
    ‖integrand σ t n‖=1/(n : ℝ)^(1+σ) := by
  by_cases hn : n=0
  · subst n
    simp [integrand,Real.zero_rpow (by linarith only [hσ] : 1+σ ≠ 0)]
  · have hp : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    rw [integrand,norm_div,numerator_norm σ t n hp,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    rw [Real.rpow_add hp,Real.rpow_one,Real.rpow_neg hp.le]
    ring

theorem summable_terms (σ t : ℝ) (hσ : 0 < σ) :
    Summable (fun n : ℕ ↦ integrand σ t n) := by
  apply Summable.of_norm
  simp_rw [term_norm σ t hσ.le]
  exact Real.summable_one_div_nat_rpow.mpr (by linarith only [hσ])

theorem split_at (σ t : ℝ) (hσ : 0 < σ) (N : ℕ) :
    series σ t=(∑ n ∈ range N, integrand σ t n)+tail σ t N := by
  exact ((summable_terms σ t hσ).sum_add_tsum_nat_add N).symm

theorem finite_tail_bound (σ t : ℝ) (hσ : 0 ≤ σ) (ht : t ≠ 0)
    (N L : ℕ) (hN : 0 < N) :
    ‖∑ k ∈ range L, integrand σ t ((k+N : ℕ) : ℝ)‖ ≤
      2*(N : ℝ)^(-σ)/|t|+2*(1+σ+|t|)*(N : ℝ)^(-σ)/(N : ℝ) := by
  have hh := DampedLogarithmicQuadrature.finite_sum_norm_bound N (N+L) hN (by omega) σ t hσ ht
  rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left] at hh
  simpa only [Nat.add_comm] using hh

theorem tail_norm_bound (σ t : ℝ) (hσ : 0 < σ) (ht : t ≠ 0)
    (N : ℕ) (hN : 0 < N) :
    ‖tail σ t N‖ ≤
      2*(N : ℝ)^(-σ)/|t|+2*(1+σ+|t|)*(N : ℝ)^(-σ)/(N : ℝ) := by
  have hSum : Summable (fun k : ℕ ↦ integrand σ t ((k+N : ℕ) : ℝ)) :=
    (summable_nat_add_iff N).mpr (summable_terms σ t hσ)
  apply le_of_tendsto hSum.hasSum.tendsto_sum_nat.norm
  exact Filter.Eventually.of_forall (fun L ↦ finite_tail_bound σ t hσ.le ht N L hN)

theorem series_difference_bound (σ t : ℝ) (hσ : 0 < σ) (ht : t ≠ 0)
    (N : ℕ) (hN : 0 < N) :
    ‖series σ t-(∑ n ∈ range N, integrand σ t n)‖ ≤
      2*(N : ℝ)^(-σ)/|t|+2*(1+σ+|t|)*(N : ℝ)^(-σ)/(N : ℝ) := by
  rw [split_at σ t hσ N,add_sub_cancel_left]
  exact tail_norm_bound σ t hσ ht N hN
end PaperP1.DampedDirichletTail
