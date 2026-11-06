module

public import PaperP1.Analysis.SupportedCoefficientSquareBudget
public import PaperP1.Analysis.DirichletRamareApproximation
public import PaperP1.Analysis.TwoPrimeBandPopulation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TwoBandDirichletApproximation
open Finset Filter MeasureTheory PaperP1 DirichletPolynomialMeanValue
open scoped Classical

theorem difference_identity (N : ℕ) (f : ℕ → ℂ) (t : ℝ) :
    value (Ico N (2*N)) f t-value (TwoPrimeBandPopulation.good N) f t=
      value (Ico N (2*N) \ TwoPrimeBandPopulation.good N) f t := by
  unfold value GaussianExponentialSums.polynomial
  exact (Finset.sum_sdiff_eq_sub (TwoPrimeBandPopulation.good_subset N)).symm

theorem difference_continuous (N : ℕ) (f : ℕ → ℂ) :
    Continuous (fun t : ℝ ↦ value (Ico N (2*N)) f t-value (TwoPrimeBandPopulation.good N) f t) :=
  (GaussianExponentialSums.polynomial_continuous (Ico N (2*N)) (fun n ↦ f n/(n : ℂ)) (fun n ↦ -Real.log n)).sub
    (GaussianExponentialSums.polynomial_continuous (TwoPrimeBandPopulation.good N) (fun n ↦ f n/(n : ℂ)) (fun n ↦ -Real.log n))

theorem difference_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1) → ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-value (TwoPrimeBandPopulation.good N) f t‖^2) ≤ ε := by
  have hlim : Tendsto (fun N : ℕ ↦ SupportedCoefficientSquareBudget.constant*
      ((Ico N (2*N) \ TwoPrimeBandPopulation.good N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero,mul_div_assoc] using
      TwoPrimeBandPopulation.missing_good_density_tendsto.const_mul SupportedCoefficientSquareBudget.constant
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro N hN f hf T hT hTN
  have hNp : 0 < N := by omega
  have hh := SupportedCoefficientSquareBudget.supported_uniform_bound N hNp
    (Ico N (2*N) \ TwoPrimeBandPopulation.good N)
    (Ico N (2*N) \ TwoPrimeBandPopulation.good N)
    sdiff_subset (fun _n hn ↦ hn) f (fun n hn ↦ hf n (sdiff_subset hn))
    (fun _n hn hnot ↦ False.elim (hnot hn)) T hT hTN
  simp_rw [difference_identity]
  exact hh.trans (by simpa only [mul_div_assoc] using (hN₀ N (by omega)).le)

def quotient (N : ℕ) (P : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, ∑ m ∈ Icc 1 (2*N/p), if p*m ∈ TwoPrimeBandPopulation.good N then
    DirichletRamareApproximation.twist f p t*DirichletRamareApproximation.twist f m t/
      ((PrimeDivisorWeights.count P m+1 : ℕ) : ℂ) else 0

theorem first_identity (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    value (TwoPrimeBandPopulation.good N) f t=
      quotient N (TwoPrimeBandPopulation.first N) f t := by
  exact TwoPrimeBandPopulation.first_ramare_sum N hN (fun n ↦ DirichletRamareApproximation.twist f n t)
    (DirichletRamareApproximation.twist_mul f hf t)

theorem second_identity (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    value (TwoPrimeBandPopulation.good N) f t=
      quotient N (TwoPrimeBandPopulation.second N) f t := by
  exact TwoPrimeBandPopulation.second_ramare_sum N hN (fun n ↦ DirichletRamareApproximation.twist f n t)
    (DirichletRamareApproximation.twist_mul f hf t)

theorem both_quotients_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-quotient N (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε ∧
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-quotient N (TwoPrimeBandPopulation.second N) f t‖^2) ≤ ε := by
  obtain ⟨N₀,hN₀,hs⟩ := difference_small_uniform ε hε
  refine ⟨N₀,hN₀,?_⟩
  intro N hN f hf hb T hT hTN
  have hNp : 0 < N := by omega
  have hh := hs N hN f hb T hT hTN
  constructor
  · simpa only [← first_identity N hNp f hf] using hh
  · simpa only [← second_identity N hNp f hf] using hh
end PaperP1.TwoBandDirichletApproximation
