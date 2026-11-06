module

public import PaperP1.Analysis.TwoBandRectangleApproximation
public import PaperP1.Analysis.FirstBandSmallRegion
public import PaperP1.Analysis.SmallPrimeRegion

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FirstGoodFullPolynomial
open Finset Filter PaperP1 MeasureTheory
open scoped Classical

theorem restricted_transfer (F R : ℝ → ℂ) (hF : Continuous F) (hR : Continuous R)
    (E : Set ℝ) (hE : MeasurableSet E) (T : ℝ) (hT : 0 ≤ T) (hsub : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖^2) ≤ 2*(∫ t in -T..T, ‖F t-R t‖^2)+2*(∫ t in E, ‖R t‖^2) := by
  have hA : Continuous (fun t ↦ ‖F t-R t‖^2) := (hF.sub hR).norm.pow 2
  have hB : Continuous (fun t ↦ ‖R t‖^2) := hR.norm.pow 2
  have hFs : Continuous (fun t ↦ ‖F t‖^2) := hF.norm.pow 2
  have hC : Continuous (fun t ↦ 2*‖F t-R t‖^2+2*‖R t‖^2) := by fun_prop
  have hi := setIntegral_mono_on (μ := volume) (f := fun t ↦ ‖F t‖^2)
    ((hFs.intervalIntegrable (-T) T).1.mono_set hsub)
    ((hC.intervalIntegrable (-T) T).1.mono_set hsub) hE (fun t _ht ↦ by
      have hn : ‖F t‖ ≤ ‖F t-R t‖+‖R t‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F t-R t) (R t)
      have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
      nlinarith only [hs,sq_nonneg (‖F t-R t‖-‖R t‖)])
  rw [integral_add (((hA.const_mul 2).intervalIntegrable (-T) T).1.mono_set hsub)
    (((hB.const_mul 2).intervalIntegrable (-T) T).1.mono_set hsub),integral_const_mul,integral_const_mul] at hi
  have he := setIntegral_mono_set (μ := volume) (hA.intervalIntegrable (-T) T).1
    (Filter.Eventually.of_forall (fun t ↦ sq_nonneg ‖F t-R t‖)) (Filter.Eventually.of_forall hsub)
  rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at he
  linarith only [hi,he]

theorem first_good_part_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, 2 ≤ H ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ → ℂ,
      (∀ a b, f (a*b)=f a*f b) → (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ∀ T : ℝ, 0 < T → T ≤ (N : ℝ)/Real.log (N : ℝ) →
      (∫ t in SmallPrimeRegion.goodSet H (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N),
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) f t‖^2) ≤ ε := by
  obtain ⟨H,hH,N₁,hN₁,happrox⟩ := TwoBandRectangleApproximation.both_rectangles_small_uniform (ε/4) (by positivity)
  obtain ⟨N₂,hN₂,hgood⟩ := FirstBandSmallRegion.small_uniform H (by omega) (ε/4) (by positivity)
  obtain ⟨NU,hU⟩ := eventually_atTop.mp (SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1))
  refine ⟨H,hH,max N₁ (max N₂ NU),by omega,?_⟩
  intro N hN f hf hb T hT hTN
  have hNp : 0 < N := by omega
  have hlog1 : 1 ≤ Real.log (N : ℝ) := hU N (by omega)
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  have hTX : T ≤ N := hTN.trans ((div_le_iff₀ hlog).mpr (by
    have hNN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith only [hlog1,hNN]))
  have hbf : ∀ n ∈ Ico N (4*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (by have := (mem_Ico.mp hn).1; omega)
  have hbi : ∀ n ∈ Icc 1 (2*N), ‖f n‖ ≤ 1 := fun n hn ↦ hb n (by have := (mem_Icc.mp hn).1; omega)
  have hr := (happrox H le_rfl N (by omega) f hf hbf T hT hTX).1
  have hg := hgood N (by omega) (TwoPrimeBandPopulation.second N) f hbi T hT hTN
  have hh := restricted_transfer
    (DirichletPolynomialMeanValue.value (Ico N (2*N)) f)
    (NarrowRamareRectangle.rectangle N H (TwoPrimeBandPopulation.first N) (TwoPrimeBandPopulation.second N) f)
    (GaussianExponentialSums.polynomial_continuous _ _ _)
    (TwoBandRectangleApproximation.rectangle_continuous _ _ _ _ _) _
    (SmallPrimeRegion.goodSet_measurable H (TwoPrimeBandPopulation.first N) f T (FirstBandSmallRegion.threshold N))
    T hT.le (fun _t ht ↦ ht.1)
  linarith only [hh,hr,hg]
end PaperP1.FirstGoodFullPolynomial
