module

public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.SupportedCoefficientSquareBudget
public import PaperP1.Analysis.RelativeRamareRemainder

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TwoBandRelativeApproximation
open Finset Filter MeasureTheory PaperP1 DirichletPolynomialMeanValue RelativeRamareRemainder
open scoped Classical

theorem both_quotients_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-
        quotient N (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) f t‖^2) ≤ ε ∧
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-
        quotient N (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  have hlim : Tendsto (fun N : ℕ ↦ SupportedCoefficientSquareBudget.constant*
      (((Ico N (2*N) \ TwoPrimeBandPopulation.good N).card : ℝ)/(N : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using
      TwoPrimeBandPopulation.missing_good_density_tendsto.const_mul SupportedCoefficientSquareBudget.constant
  obtain ⟨NL,hL⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  obtain ⟨ND,hD⟩ := eventually_atTop.mp TwoPrimeBandPopulation.disjoint_eventually
  refine ⟨max 1 (max NL ND),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hNp : 0 < N := by omega
  let E := Ico N (2*N) \ TwoPrimeBandPopulation.good N
  have hsmall : SupportedCoefficientSquareBudget.constant*((E.card : ℝ)/(N : ℝ)) ≤ ε :=
    (hL N (by omega)).le
  have hBound (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
      (hZero : ∀ n ∈ TwoPrimeBandPopulation.good N, residual P Q n=0) :
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-quotient N P Q f t‖^2) ≤ ε := by
    have hz : ∀ n ∈ Ico N (2*N), n ∉ E → coefficient P Q f n=0 := by
      intro n hn hnE
      have hg : n ∈ TwoPrimeBandPopulation.good N := by
        by_contra hnot
        exact hnE (Finset.mem_sdiff.mpr ⟨hn,hnot⟩)
      rw [coefficient,hZero n hg,Complex.ofReal_zero,zero_mul]
    have hh := SupportedCoefficientSquareBudget.supported_uniform_bound N hNp (Ico N (2*N)) E
      (fun _n hn ↦ hn) (show E ⊆ Ico N (2*N) from Finset.sdiff_subset) (coefficient P Q f)
      (fun n hn ↦ coefficient_norm_bound P Q hP f n (hb n hn)) hz T hT hTN
    simp_rw [difference_identity N hNp P Q hP hQ hPQ f hf]
    exact hh.trans hsmall
  have hP : ∀ p ∈ TwoPrimeBandPopulation.first N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hQ : ∀ p ∈ TwoPrimeBandPopulation.second N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hPQ := hD N (by omega)
  constructor
  · apply hBound (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) hP hQ hPQ
    intro n hn
    have hg := TwoPrimeBandPopulation.good_support N hNp n hn
    exact residual_eq_zero _ _ hP n hg.2.1 hg.2.2.1 hg.2.2.2.1
  · apply hBound (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) hQ hP hPQ.symm
    intro n hn
    have hg := TwoPrimeBandPopulation.good_support N hNp n hn
    exact residual_eq_zero _ _ hQ n hg.2.2.1 hg.2.1 hg.2.2.2.2
end PaperP1.TwoBandRelativeApproximation
