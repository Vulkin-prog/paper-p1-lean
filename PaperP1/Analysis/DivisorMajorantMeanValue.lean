module

public import PaperP1.Analysis.CenteredLogarithmicSampling
public import PaperP1.Analysis.WeightedDivisorSquare

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DivisorMajorantMeanValue
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem coefficient_square_bound {ι : Type*} (I : Finset ι) (d : ι → ℕ) (w : ι → ℝ)
    (hd : ∀ a ∈ I, 0 < d a) (hw : ∀ a ∈ I, 0 ≤ w a)
    (L M : ℕ) (hL : 0 < L) (S : Finset ℕ) (hS : S ⊆ Icc L M) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ WeightedDivisorSquare.divisorSum I d w n) :
    (∑ n ∈ S, ‖a n/(n : ℂ)‖^2) ≤
      ((M : ℝ)/(L : ℝ)^2)*WeightedDivisorSquare.kernel I d w := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : S ⊆ Ioc 0 M := by
    intro n hn
    have hm := mem_Icc.mp (hS hn)
    exact mem_Ioc.mpr ⟨by omega,hm.2⟩
  have hterm (n : ℕ) (hn : n ∈ S) :
      ‖a n/(n : ℂ)‖^2 ≤ (WeightedDivisorSquare.divisorSum I d w n)^2/(L : ℝ)^2 := by
    have hnL : (L : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (hS hn)).1
    have hD := WeightedDivisorSquare.divisorSum_nonneg I d w hw n
    have hh : ‖a n/(n : ℂ)‖ ≤ WeightedDivisorSquare.divisorSum I d w n/(L : ℝ) := by
      rw [norm_div,Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (ha n hn) (Nat.cast_nonneg n)).trans
        (div_le_div_of_nonneg_left hD hLp hnL)
    simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hext : (∑ n ∈ S, (WeightedDivisorSquare.divisorSum I d w n)^2) ≤
      ∑ n ∈ Ioc 0 M, (WeightedDivisorSquare.divisorSum I d w n)^2 :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n hn hnot ↦ sq_nonneg _)
  calc
    _ ≤ ∑ n ∈ S, (WeightedDivisorSquare.divisorSum I d w n)^2/(L : ℝ)^2 := sum_le_sum hterm
    _ = (1/(L : ℝ)^2)*(∑ n ∈ S, (WeightedDivisorSquare.divisorSum I d w n)^2) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      ring
    _ ≤ (1/(L : ℝ)^2)*((M : ℝ)*WeightedDivisorSquare.kernel I d w) :=
      mul_le_mul_of_nonneg_left (hext.trans (WeightedDivisorSquare.square_sum_bound I d w hd hw M)) (by positivity)
    _ = _ := by ring

theorem mean_value_bound {ι : Type*} (I : Finset ι) (d : ι → ℕ) (w : ι → ℝ)
    (hd : ∀ a ∈ I, 0 < d a) (hw : ∀ a ∈ I, 0 ≤ w a)
    (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (S : Finset ℕ) (hS : S ⊆ Icc L M) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ WeightedDivisorSquare.divisorSum I d w n)
    (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value S a t‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*T+2*Real.pi*(M : ℝ))*
        (((M : ℝ)/(L : ℝ)^2)*WeightedDivisorSquare.kernel I d w) := by
  have hh := DirichletPolynomialMeanValue.logarithmic_interval_bound S (fun n ↦ a n/(n : ℂ)) M hM
    (by intro n hn; have hm := mem_Icc.mp (hS hn); exact ⟨by omega,hm.2⟩) T hT
  exact hh.trans (mul_le_mul_of_nonneg_left (coefficient_square_bound I d w hd hw L M hL S hS a ha) (by positivity))

theorem sampled_mean_value_bound {α ι : Type*} (I : Finset ι) (d : ι → ℕ) (w : ι → ℝ)
    (hd : ∀ a ∈ I, 0 < d a) (hw : ∀ a ∈ I, 0 ≤ w a)
    (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (S : Finset ℕ) (hS : S ⊆ Icc L M) (a : ℕ → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ WeightedDivisorSquare.divisorSum I d w n)
    (R : Finset α) (τ : α → ℝ) (T : ℝ) (hT : 0 < T)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value S a (τ r)‖^2) ≤
      Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*(M : ℝ))*
        (2+(Real.log (M : ℝ)-Real.log (L : ℝ))^2)*
        (((M : ℝ)/(L : ℝ)^2)*WeightedDivisorSquare.kernel I d w) := by
  have hh := CenteredLogarithmicSampling.integer_band_sampled_mean_square R τ T hT htau hsep S
    (fun n ↦ a n/(n : ℂ)) L M hL hM (fun n hn ↦ mem_Icc.mp (hS hn))
  exact hh.trans (mul_le_mul_of_nonneg_left (coefficient_square_bound I d w hd hw L M hL S hS a ha) (by positivity))
end PaperP1.DivisorMajorantMeanValue
