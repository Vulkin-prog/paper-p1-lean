module

public import PaperP1.Arithmetic.RamareWeights
public import PaperP1.Analysis.SupportedCoefficientSquareBudget

/-! # An unconditional uniform negligible Ramare residual in actual Dirichlet mean square -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RamareRemainderMeanValue
open Finset Filter PaperP1 SlowPrimeBandSieve
open scoped Classical

def coefficient (P : Finset ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((1-RamareWeights.weight P n : ℝ) : ℂ)*a n

theorem coefficient_norm_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℕ → ℂ) (n : ℕ) (ha : ‖a n‖ ≤ 1) : ‖coefficient P a n‖ ≤ 1 := by
  rw [coefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (RamareWeights.residual_nonneg P hP n)]
  exact (mul_le_mul (RamareWeights.residual_le_one P n) ha (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem coefficient_good_zero (N : ℕ) (hN : 0 < N) (a : ℕ → ℂ) (n : ℕ) (hn : n ∈ good N) :
    coefficient (primes N) a n=0 := by
  rw [coefficient,RamareWeights.residual_good_zero N hN n hn,Complex.ofReal_zero,zero_mul]

theorem remainder_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ a : ℕ → ℂ, (∀ n ∈ Ico N (2*N), ‖a n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N))
        (coefficient (primes N) a) t‖^2) ≤ ε := by
  have hlim : Tendsto (fun N : ℕ ↦ SupportedCoefficientSquareBudget.constant*
      ((Ico N (2*N) \ good N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,mul_div_assoc] using
      missing_good_density_tendsto.const_mul SupportedCoefficientSquareBudget.constant
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro N hN a ha T hT hTN
  have hNpos : 0 < N := by omega
  have hzero : ∀ n ∈ Ico N (2*N), n ∉ Ico N (2*N) \ good N → coefficient (primes N) a n=0 := by
    intro n hn hnot
    have hg : n ∈ good N := by
      by_contra hng
      exact hnot (mem_sdiff.mpr ⟨hn,hng⟩)
    exact coefficient_good_zero N hNpos a n hg
  have hh := SupportedCoefficientSquareBudget.supported_uniform_bound N hNpos (Ico N (2*N))
    (Ico N (2*N) \ good N) (fun n hn ↦ hn) sdiff_subset (coefficient (primes N) a)
    (fun n hn ↦ coefficient_norm_le_one (primes N) (fun p hp ↦ (mem_filter.mp hp).2) a n (ha n hn))
    hzero T hT hTN
  have hsmall := (hN₀ N (by omega)).le
  rw [mul_div_assoc] at hsmall
  exact hh.trans hsmall
end RamareRemainderMeanValue
