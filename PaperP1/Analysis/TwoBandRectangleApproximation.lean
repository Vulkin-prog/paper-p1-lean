module

public import PaperP1.Analysis.TwoBandRelativeApproximation
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.NarrowRectangleError

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TwoBandRectangleApproximation
open Finset Filter MeasureTheory PaperP1
open scoped Classical

theorem rectangle_continuous (X H : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) :
    Continuous (NarrowRamareRectangle.rectangle X H P Q f) := by
  apply continuous_finsetSum
  intro j hj
  exact (GaussianExponentialSums.polynomial_continuous _ _ _).mul
    (GaussianExponentialSums.polynomial_continuous _ _ _)

theorem mean_square_triangle (F G K : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hK : Continuous K) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖F t-K t‖^2) ≤
      2*(∫ t in -T..T, ‖F t-G t‖^2)+2*(∫ t in -T..T, ‖K t-G t‖^2) := by
  have hA : Continuous (fun t ↦ ‖F t-G t‖^2) := (hF.sub hG).norm.pow 2
  have hB : Continuous (fun t ↦ ‖K t-G t‖^2) := (hK.sub hG).norm.pow 2
  have hC : Continuous (fun t ↦ ‖F t-K t‖^2) := (hF.sub hK).norm.pow 2
  have hD : Continuous (fun t ↦ 2*‖F t-G t‖^2+2*‖K t-G t‖^2) := by fun_prop
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -T ≤ T)
    (hC.intervalIntegrable (-T) T) (hD.intervalIntegrable (-T) T) (fun t _ht ↦ by
      have he : F t-K t=(F t-G t)-(K t-G t) := by abel
      have hn : ‖F t-K t‖ ≤ ‖F t-G t‖+‖K t-G t‖ := by rw [he]; exact norm_sub_le _ _
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      nlinarith only [hs,sq_nonneg (‖F t-G t‖-‖K t-G t‖)])
  rw [intervalIntegral.integral_add (hA.const_mul 2 |>.intervalIntegrable (-T) T)
    (hB.const_mul 2 |>.intervalIntegrable (-T) T),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hh
  exact hh

theorem both_rectangles_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ H ≥ H₀, ∀ N ≥ N₀,
      ∀ f : ℕ → ℂ, (∀ a b, f (a*b)=f a*f b) → (∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ N →
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) f t‖^2) ≤ ε ∧
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.second N) (TwoPrimeBandPopulation.first N) f t‖^2) ≤ ε := by
  obtain ⟨H₀,hH₀,X₀,hX₀,hrect⟩ := NarrowRectangleError.small_uniform (ε/4) (by positivity)
  obtain ⟨N₁,hN₁,hquot⟩ := TwoBandRelativeApproximation.both_quotients_small_uniform (ε/4) (by positivity)
  obtain ⟨ND,hD⟩ := eventually_atTop.mp TwoPrimeBandPopulation.disjoint_eventually
  refine ⟨H₀,hH₀,max X₀ (max N₁ ND),by omega,?_⟩
  intro H hH N hN f hf hb T hT hTN
  have hbd : ∀ n ∈ Ico N (2*N), ‖f n‖ ≤ 1 := by
    intro n hn
    apply hb n
    have hh := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨hh.1,by omega⟩
  obtain ⟨hq₁,hq₂⟩ := hquot N (by omega) f hf hbd T hT hTN
  have hP : ∀ p ∈ TwoPrimeBandPopulation.first N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hQ : ∀ q ∈ TwoPrimeBandPopulation.second N, q.Prime := fun q hq ↦ (mem_filter.mp hq).2
  have hPQ := hD N (by omega)
  have hF : Continuous (DirichletPolynomialMeanValue.value (Ico N (2*N)) f) :=
    GaussianExponentialSums.polynomial_continuous _ _ _
  have hBound (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
      (hq : (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        RelativeRamareRemainder.quotient N P Q f t‖^2) ≤ ε/4) :
      (∫ t in -T..T, ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t-
        NarrowRamareRectangle.rectangle N H P Q f t‖^2) ≤ ε := by
    have hr := hrect H hH N (by omega) P Q hP hQ hPQ f hf hb T hT hTN
    have hh := mean_square_triangle _ _ _ hF (RelativeRamareRemainder.quotient_continuous N P Q f)
      (rectangle_continuous N H P Q f) T hT.le
    linarith only [hh,hq,hr]
  exact ⟨hBound _ _ hP hQ hPQ hq₁,hBound _ _ hQ hP hPQ.symm hq₂⟩
end PaperP1.TwoBandRectangleApproximation
