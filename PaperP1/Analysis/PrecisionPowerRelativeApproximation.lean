module

public import PaperP1.Analysis.SupportedCoefficientSquareBudget
public import PaperP1.Analysis.RelativeRamareRemainder
public import PaperP1.Analysis.PrecisionPowerPopulation


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrecisionPowerRelativeApproximation
open Finset Filter MeasureTheory PaperP1 DirichletPolynomialMeanValue RelativeRamareRemainder
open scoped Classical

theorem quantitative_bound (a b : ℝ) (N : ℕ) (hN : 0 < N)
    (hPQ : Disjoint (FixedPowerPrimeBand.primes a b N) (TwoPrimeBandPopulation.first N))
    (f : ℕ → ℂ) (hf : ∀ m n, f (m*n)=f m*f n) (hb : ∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1)
    (T : ℝ) (hT : 0 < T) (hTN : T ≤ N) :
    (∫ t in -T..T, ‖value (Ico N (2*N)) f t-
      quotient N (FixedPowerPrimeBand.primes a b N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤
      SupportedCoefficientSquareBudget.constant*((Ico N (2*N) \ PrecisionPowerPopulation.good a b N).card : ℝ)/(N : ℝ) := by
  let P := FixedPowerPrimeBand.primes a b N
  let Q := TwoPrimeBandPopulation.first N
  let E := Ico N (2*N) \ PrecisionPowerPopulation.good a b N
  have hP : ∀ p ∈ P, p.Prime := fun p hp ↦ (FixedPowerPrimeBand.mem_primes a b N p hp).1
  have hQ : ∀ q ∈ Q, q.Prime := fun q hq ↦ (mem_filter.mp hq).2
  have hz : ∀ n ∈ Ico N (2*N), n ∉ E → coefficient P Q f n=0 := by
    intro n hn hnE
    have hGood : n ∈ PrecisionPowerPopulation.good a b N := by
      by_contra hnot
      exact hnE (Finset.mem_sdiff.mpr ⟨hn,hnot⟩)
    have hg := PrecisionPowerPopulation.good_support a b N hN n hGood
    rw [coefficient,residual_eq_zero P Q hP n hg.2.2.1 hg.2.1 hg.2.2.2,Complex.ofReal_zero,zero_mul]
  have hh := SupportedCoefficientSquareBudget.supported_uniform_bound N hN (Ico N (2*N)) E
    (fun _ hn ↦ hn) (Finset.sdiff_subset) (coefficient P Q f)
    (fun n hn ↦ coefficient_norm_bound P Q hP f n (hb n hn)) hz T hT hTN
  change (∫ t in -T..T, ‖value (Ico N (2*N)) f t-quotient N P Q f t‖^2) ≤
    SupportedCoefficientSquareBudget.constant*(E.card : ℝ)/(N : ℝ)
  simp_rw [difference_identity N hN P Q hP hQ hPQ f hf]
  exact hh.trans_eq (by ring)

theorem precision_choice (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1/32 ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ f : ℕ → ℂ, (∀ m n, f (m*n)=f m*f n) → (∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖value (Ico N (2*N)) f t-
        quotient N (FixedPowerPrimeBand.primes a (1/32) N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  have hC := SupportedCoefficientSquareBudget.constant_pos
  obtain ⟨a,ha,hab,hDensity⟩ := PrecisionPowerPopulation.precision_choice
    (ε/SupportedCoefficientSquareBudget.constant) (div_pos hε hC)
  obtain ⟨NL,hL⟩ := eventually_atTop.mp hDensity
  obtain ⟨ND,hD⟩ := eventually_atTop.mp (PrecisionPowerPopulation.disjoint_first_eventually a (1/32) ha)
  refine ⟨a,ha,hab,max 1 (max NL ND),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hActual := quantitative_bound a (1/32) N (by omega) (hD N (by omega)) f hf hb T hT hTN
  have hSmall := mul_le_mul_of_nonneg_left (hL N (by omega)) hC.le
  have he : SupportedCoefficientSquareBudget.constant*(ε/SupportedCoefficientSquareBudget.constant)=ε := by field_simp [hC.ne']
  calc
    _ ≤ SupportedCoefficientSquareBudget.constant*((Ico N (2*N) \ PrecisionPowerPopulation.good a (1/32) N).card : ℝ)/(N : ℝ) := hActual
    _ = SupportedCoefficientSquareBudget.constant*(((Ico N (2*N) \ PrecisionPowerPopulation.good a (1/32) N).card : ℝ)/(N : ℝ)) := by ring
    _ ≤ _ := hSmall.trans_eq he
end PaperP1.PrecisionPowerRelativeApproximation
