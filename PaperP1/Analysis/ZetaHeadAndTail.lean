module

public import PaperP1.Analysis.DampedDirichletTail
public import PaperP1.Analysis.ActualZetaTail
public import PaperP1.Analysis.LogarithmicDifferencingBound
public import PaperP1.Analysis.ZetaCutoffGeometry

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ZetaHeadAndTail
open Finset Filter MeasureTheory PaperP1 DampedLogarithmicIntegral ZetaCutoffGeometry
open scoped Classical

theorem head_norm_bound (N : ℕ) (hN : 1 ≤ N) (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖∑ n ∈ range N, integrand σ t n‖ ≤ 1+Real.log (N : ℝ) := by
  have hHead : (∑ n ∈ range N, integrand σ t n)=∑ n ∈ Ico 1 N, integrand σ t n := by
    have hh := sum_Ico_consecutive (fun n : ℕ ↦ integrand σ t n) (show 0 ≤ 1 by decide) hN
    simpa [Nat.Ico_zero_eq_range,integrand] using hh.symm
  rw [hHead]
  calc
    _ ≤ ∑ n ∈ Ico 1 N, ‖integrand σ t n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Ico 1 N, 1/(n : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      have hnp : (0 : ℝ) < n := by linarith only [hn1]
      have hPow : (n : ℝ) ≤ (n : ℝ)^(1+σ) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (show (1 : ℝ) ≤ 1+σ by linarith only [hσ])
      rw [DampedDirichletTail.term_norm σ t hσ n]
      exact one_div_le_one_div_of_le hnp hPow
    _ ≤ ∑ n ∈ Icc 1 N, 1/(n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (by intro n hn; exact mem_Icc.mpr ⟨(mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩)
        (by intros; positivity)
    _ ≤ _ := LogarithmicDifferencingBound.harmonic_bound N

theorem head_split (N M : ℕ) (hNM : N ≤ M) (σ t : ℝ) :
    (∑ n ∈ range M, integrand σ t n)=
      (∑ n ∈ range N, integrand σ t n)+(∑ n ∈ Ico N M, integrand σ t n) := by
  have hh := sum_Ico_consecutive (fun n : ℕ ↦ integrand σ t n) (show 0 ≤ N by omega) hNM
  simpa only [Nat.Ico_zero_eq_range] using hh.symm

theorem rounded_head_bound (α y : ℝ) (hα : 0 ≤ α) (hy : 1 ≤ y) (σ t : ℝ) (hσ : 0 ≤ σ) :
    ‖∑ n ∈ range (lower α y), integrand σ t n‖ ≤ 1+Real.log 2+α*Real.log y := by
  have hh := head_norm_bound (lower α y) (lower_bounds α y hα hy).1 σ t hσ
  linarith only [hh,logarithmic_lower α y hα hy]

theorem rounded_tail_bound (σ t : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (ht : 1 ≤ |t|) :
    ‖riemannZeta (ActualZetaTail.argument σ t)-
      (∑ n ∈ range (upper |t|), integrand σ t n)‖ ≤ 8/|t| := by
  have htP : 0 < |t| := by linarith only [ht]
  have hUp := upper_bounds |t| ht
  have hUR : (1 : ℝ) ≤ upper |t| := by exact_mod_cast hUp.1
  have hUP : (0 : ℝ) < upper |t| := by linarith only [hUR]
  have hPow : (upper |t| : ℝ)^(-σ) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hUR (show -σ ≤ 0 by linarith only [hσ0])
  have hBound := ActualZetaTail.zeta_difference_bound σ t hσ0 (abs_pos.mp htP)
    (upper |t|) (by omega)
  have hFirst : 2*(upper |t| : ℝ)^(-σ)/|t| ≤ 2/|t| := by
    exact div_le_div_of_nonneg_right (by linarith only [hPow]) (abs_nonneg t)
  have hSecond : 2*(1+σ+|t|)*(upper |t| : ℝ)^(-σ)/(upper |t| : ℝ) ≤ 6/|t| := by
    calc
      _ ≤ 2*(2+|t|)/(upper |t| : ℝ) := div_le_div_of_nonneg_right (by
        have hh := mul_le_mul_of_nonneg_left hPow (by positivity : 0 ≤ 2*(1+σ+|t|))
        nlinarith only [hh,hσ1]) hUP.le
      _ ≤ 2*(2+|t|)/|t|^2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos htP) hUp.2.1
      _ ≤ _ := by
        apply (div_le_div_iff₀ (sq_pos_of_pos htP) htP).mpr
        nlinarith only [ht,mul_nonneg (sub_nonneg.mpr ht) htP.le]
  exact hBound.trans ((add_le_add hFirst hSecond).trans_eq (by ring))
end PaperP1.ZetaHeadAndTail
