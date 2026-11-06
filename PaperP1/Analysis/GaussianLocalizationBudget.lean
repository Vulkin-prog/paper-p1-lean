module

public import PaperP1.Analysis.LogarithmicGaussianSum
public import PaperP1.Analysis.ScaledGaussianKernel


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianLocalizationBudget
open Finset PaperP1 GaussianOverlap GaussianLaplaceKernel ScaledGaussianKernel
open scoped Classical

theorem exponential_comparison (δ v : ℝ) (hδ : 0 < δ) :
    Real.exp (-v^2/(8*δ^2)) ≤ Real.exp (-v^2/(32*δ^2)) := by
  apply Real.exp_le_exp.mpr
  have hh : 0 ≤ v^2/(32*δ^2) := by positivity
  have he : -v^2/(8*δ^2) = -4*(v^2/(32*δ^2)) := by ring
  rw [he,show -v^2/(32*δ^2)=-(v^2/(32*δ^2)) by ring]
  nlinarith only [hh]

theorem tail_sum (S : Finset ℕ) (a : ℕ → ℝ) (A X δ m : ℝ)
    (hA : 0 ≤ A) (hX : 0 < X) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m)
    (hS : ∀ n ∈ S, 0 < n) (ha : ∀ n ∈ S, 0 ≤ a n ∧ a n ≤ A)
    (hAway : ∀ n ∈ S, m ≤ |Real.log ((n : ℝ)/X)|) :
    (∑ n ∈ S, a n*heat (δ^2) (Real.log ((n : ℝ)/X))) ≤
      Real.exp (-m^2/(8*δ^2))*A*(prefactor 1/δ)*
        LogarithmicGaussianSum.constant*(δ*X+1) := by
  have hPref : 0 ≤ prefactor 1/δ := by positivity [prefactor_pos 1 (by norm_num)]
  have hFactor : 0 ≤ Real.exp (-m^2/(8*δ^2))*A*(prefactor 1/δ) := by positivity
  calc
    _ ≤ ∑ n ∈ S, Real.exp (-m^2/(8*δ^2))*A*(prefactor 1/δ)*
        LogarithmicGaussianSum.logGaussian X δ n := by
      apply sum_le_sum
      intro n hn
      have hKernel := (heat_tail δ m (Real.log ((n : ℝ)/X)) hδ hm (hAway n hn)).trans
        (mul_le_mul_of_nonneg_left (exponential_comparison δ (Real.log ((n : ℝ)/X)) hδ)
          (mul_nonneg (Real.exp_pos _).le hPref))
      have hStep := mul_le_mul (ha n hn).2 hKernel (heat_nonneg _ _ (sq_pos_of_pos hδ)) hA
      dsimp only [LogarithmicGaussianSum.logGaussian]
      nlinarith only [hStep]
    _ = (Real.exp (-m^2/(8*δ^2))*A*(prefactor 1/δ))*
        ∑ n ∈ S, LogarithmicGaussianSum.logGaussian X δ n := by rw [mul_sum]
    _ ≤ (Real.exp (-m^2/(8*δ^2))*A*(prefactor 1/δ))*
        (LogarithmicGaussianSum.constant*(δ*X+1)) :=
      mul_le_mul_of_nonneg_left (LogarithmicGaussianSum.finite_logGaussian_sum S X δ hX hδ hδ1 hS) hFactor
    _ = _ := by ring

theorem sum_bound (S : Finset ℕ) (a : ℕ → ℝ) (A X δ : ℝ)
    (hA : 0 ≤ A) (hX : 0 < X) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hS : ∀ n ∈ S, 0 < n) (ha : ∀ n ∈ S, 0 ≤ a n ∧ a n ≤ A) :
    (∑ n ∈ S, a n*heat (δ^2) (Real.log ((n : ℝ)/X))) ≤
      A*(prefactor 1/δ)*LogarithmicGaussianSum.constant*(δ*X+1) := by
  simpa only [zero_pow (by decide : (2 : ℕ)≠0),neg_zero,zero_div,Real.exp_zero,one_mul] using
    tail_sum S a A X δ 0 hA hX hδ hδ1 le_rfl hS ha (fun n hn ↦ abs_nonneg _)

theorem one_point_bound (S : Finset ℕ) (a : ℕ → ℝ) (A X δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hCard : S.card ≤ 1)
    (ha : ∀ n ∈ S, 0 ≤ a n ∧ a n ≤ A) :
    (∑ n ∈ S, a n*heat (δ^2) (Real.log ((n : ℝ)/X))) ≤ A*(prefactor 1/δ) := by
  have hPref : 0 ≤ prefactor 1/δ := by positivity [prefactor_pos 1 (by norm_num)]
  calc
    _ ≤ ∑ _n ∈ S, A*(prefactor 1/δ) := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul (ha n hn).2 (heat_upper δ _ hδ)
        (heat_nonneg _ _ (sq_pos_of_pos hδ)) hA
    _ = (S.card : ℝ)*(A*(prefactor 1/δ)) := by rw [sum_const,nsmul_eq_mul]
    _ ≤ 1*(A*(prefactor 1/δ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) (mul_nonneg hA hPref)
    _ = _ := one_mul _

theorem localization (S I : Finset ℕ) (hIS : I ⊆ S) (a : ℕ → ℝ) (A X δ m : ℝ)
    (hA : 0 ≤ A) (hX : 0 < X) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m)
    (hS : ∀ n ∈ S, 0 < n) (ha : ∀ n ∈ S, 0 ≤ a n ∧ a n ≤ A)
    (hCard : I.card ≤ 1) (hAway : ∀ n ∈ S \ I, m ≤ |Real.log ((n : ℝ)/X)|) :
    (∑ n ∈ S, a n*heat (δ^2) (Real.log ((n : ℝ)/X))) ≤
      A*(prefactor 1/δ)+Real.exp (-m^2/(8*δ^2))*A*(prefactor 1/δ)*
        LogarithmicGaussianSum.constant*(δ*X+1) := by
  have hSplit := sum_sdiff hIS (f := fun n ↦ a n*heat (δ^2) (Real.log ((n : ℝ)/X)))
  have hInside := one_point_bound I a A X δ hA hδ hCard (fun n hn ↦ ha n (hIS hn))
  have hOutside := tail_sum (S \ I) a A X δ m hA hX hδ hδ1 hm
    (fun n hn ↦ hS n (mem_sdiff.mp hn).1) (fun n hn ↦ ha n (mem_sdiff.mp hn).1) hAway
  linarith only [hSplit,hInside,hOutside]

end PaperP1.GaussianLocalizationBudget
