module

public import PaperP1.Analysis.NarrowRectangleError
public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.PrecisionPowerPopulation
public import PaperP1.Analysis.PrecisionPowerRelativeApproximation


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrecisionPowerRectangleApproximation
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem precision_choice (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1/32 ∧ ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ H ≥ H₀, ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ m n, f (m*n)=f m*f n) → (∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a (1/32) N)
          (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  obtain ⟨a,ha,hab,NQ,hNQ,hQuotient⟩ := PrecisionPowerRelativeApproximation.precision_choice (ε/4) (by positivity)
  obtain ⟨H₀,hH₀,NR,hNR,hRectangle⟩ := NarrowRectangleError.small_uniform (ε/4) (by positivity)
  obtain ⟨ND,hDisjoint⟩ := eventually_atTop.mp (PrecisionPowerPopulation.disjoint_first_eventually a (1/32) ha)
  refine ⟨a,ha,hab,H₀,hH₀,max NQ (max NR ND),by omega,?_⟩
  intro H hH N hN f hf hb T hT hTN
  have hNP : 0 < N := by omega
  let P := FixedPowerPrimeBand.primes a (1/32) N
  let Q := TwoPrimeBandPopulation.first N
  have hP : ∀ p ∈ P, p.Prime := fun p hp ↦ (FixedPowerPrimeBand.mem_primes a (1/32) N p hp).1
  have hQ : ∀ q ∈ Q, q.Prime := fun q hq ↦ (mem_filter.mp hq).2
  have hPQ : Disjoint P Q := hDisjoint N (by omega)
  have hNarrow : ∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1 := by
    intro n hn
    apply hb n
    have hh := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨hh.1,by omega⟩
  have hq := hQuotient N (by omega) f hf hNarrow T hT hTN
  have hr := hRectangle H hH N (by omega) P Q hP hQ hPQ f hf hb T hT hTN
  have hTriangle := TwoBandRectangleApproximation.mean_square_triangle
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (RelativeRamareRemainder.quotient N P Q f) (NarrowRamareRectangle.rectangle N H P Q f)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (RelativeRamareRemainder.quotient_continuous N P Q f)
    (TwoBandRectangleApproximation.rectangle_continuous N H P Q f) T hT.le
  dsimp only [P,Q] at hTriangle hr
  linarith only [hTriangle,hq,hr]
end PaperP1.PrecisionPowerRectangleApproximation
