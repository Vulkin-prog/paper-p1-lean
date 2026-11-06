module

public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.FinalPrimeBandGeometry
public import PaperP1.Analysis.FinalPrimeBandPopulation
public import PaperP1.Analysis.FinalRelativeApproximation

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalRectangleApproximation
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem rectangle_small_uniform (B : ℕ) (hB : 32 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ H ≥ H₀, ∀ N ≥ N₀,
      ∀ f : ℕ → ℂ, (∀ a b, f (a*b)=f a*f b) → (∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        NarrowRamareRectangle.rectangle N H (FinalPrimeBandGeometry.primes B N)
          (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  obtain ⟨H₀,hH₀,X₀,hX₀,hrect⟩ := NarrowRectangleError.small_uniform (ε/4) (by positivity)
  obtain ⟨N₁,hN₁,hquot⟩ := FinalRelativeApproximation.quotient_small_uniform B hB (ε/4) (by positivity)
  obtain ⟨ND,hD⟩ := eventually_atTop.mp (FinalPrimeBandPopulation.disjoint_first_eventually B)
  refine ⟨H₀,hH₀,max X₀ (max N₁ ND),by omega,?_⟩
  intro H hH N hN f hf hb T hT hTN
  have hbd : ∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1 := by
    intro n hn
    apply hb n
    have hh := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨hh.1,by omega⟩
  have hq := hquot N (by omega) f hf hbd T hT hTN
  have hP : ∀ p ∈ FinalPrimeBandGeometry.primes B N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hQ : ∀ q ∈ TwoPrimeBandPopulation.first N, q.Prime := fun q hq ↦ (mem_filter.mp hq).2
  have hPQ := hD N (by omega)
  have hr := hrect H hH N (by omega) _ _ hP hQ hPQ f hf hb T hT hTN
  have hF : Continuous (DirichletPolynomialMeanValue.value (Ico N (2*N)) f) :=
    GaussianExponentialSums.polynomial_continuous _ _ _
  have hh := TwoBandRectangleApproximation.mean_square_triangle _ _ _ hF
    (RelativeRamareRemainder.quotient_continuous N (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f)
    (TwoBandRectangleApproximation.rectangle_continuous N H (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) f) T hT.le
  linarith only [hh,hq,hr]
end PaperP1.FinalRectangleApproximation
