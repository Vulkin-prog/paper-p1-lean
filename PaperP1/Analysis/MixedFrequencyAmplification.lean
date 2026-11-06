module

public import PaperP1.Analysis.DirichletProductMeanValue

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.MixedFrequencyAmplification
open PaperP1 MeasureTheory
open scoped Classical

def mixedSet (A D : ℝ → ℂ) (T v w : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc (-T) T ∧ v ≤ ‖A t‖ ∧ ‖D t‖ ≤ w}

theorem pointwise_bound (k : ℕ) (A D F : ℂ) (v w : ℝ) (hv : 0 < v) (hw : 0 ≤ w)
    (hA : v ≤ ‖A‖) (hD : ‖D‖ ≤ w) :
    ‖D*F‖^2 ≤ (w^2/v^(2*k))*‖A^k*F‖^2 := by
  have hp := pow_le_pow_left₀ hv.le hA (2*k)
  have hq := (sq_le_sq₀ (norm_nonneg D) hw).mpr hD
  have hm := mul_le_mul hp hq (sq_nonneg ‖D‖) (pow_nonneg (norm_nonneg A) (2*k))
  have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖F‖)
  have hnorm : ‖A^k*F‖^2=‖A‖^(2*k)*‖F‖^2 := by
    rw [norm_mul,mul_pow,norm_pow,← pow_mul,Nat.mul_comm k 2]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hv (2*k))).mpr
  calc
    _ = (v^(2*k)*‖D‖^2)*‖F‖^2 := by rw [norm_mul,mul_pow]; ring
    _ ≤ (‖A‖^(2*k)*w^2)*‖F‖^2 := hm'
    _ = _ := by rw [hnorm]; ring

theorem restricted_bound (k : ℕ) (A D F : ℝ → ℂ) (hA : Continuous A) (hD : Continuous D)
    (hF : Continuous F) (E : Set ℝ) (hE : MeasurableSet E) (T v w : ℝ)
    (hT : 0 ≤ T) (hv : 0 < v) (hw : 0 ≤ w) (hsub : E ⊆ Set.Ioc (-T) T)
    (hbig : ∀ t ∈ E, v ≤ ‖A t‖) (hsmall : ∀ t ∈ E, ‖D t‖ ≤ w) :
    (∫ t in E, ‖D t*F t‖^2) ≤ (w^2/v^(2*k))*(∫ t in -T..T, ‖A t^k*F t‖^2) := by
  let c := w^2/v^(2*k)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hDF : Continuous (fun t ↦ ‖D t*F t‖^2) := (hD.mul hF).norm.pow 2
  have hAF : Continuous (fun t ↦ ‖A t^k*F t‖^2) := ((hA.pow k).mul hF).norm.pow 2
  have hCF : Continuous (fun t ↦ c*‖A t^k*F t‖^2) := continuous_const.mul hAF
  have hi := setIntegral_mono_on (μ := volume) (f := fun t ↦ ‖D t*F t‖^2)
    (g := fun t ↦ c*‖A t^k*F t‖^2) ((hDF.intervalIntegrable (-T) T).1.mono_set hsub)
    ((hCF.intervalIntegrable (-T) T).1.mono_set hsub) hE
    (fun t ht ↦ pointwise_bound k (A t) (D t) (F t) v w hv hw (hbig t ht) (hsmall t ht))
  rw [integral_const_mul] at hi
  have he := setIntegral_mono_set (μ := volume) (hAF.intervalIntegrable (-T) T).1
    (Filter.Eventually.of_forall (fun t ↦ sq_nonneg ‖A t^k*F t‖)) (Filter.Eventually.of_forall hsub)
  rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at he
  exact hi.trans (mul_le_mul_of_nonneg_left he hc)

theorem mixedSet_measurable (A D : ℝ → ℂ) (hA : Continuous A) (hD : Continuous D) (T v w : ℝ) :
    MeasurableSet (mixedSet A D T v w) :=
  measurableSet_Ioc.inter ((isClosed_le continuous_const hA.norm).measurableSet.inter
    (isClosed_le hD.norm continuous_const).measurableSet)

theorem mixedSet_bound (k : ℕ) (A D F : ℝ → ℂ) (hA : Continuous A) (hD : Continuous D)
    (hF : Continuous F) (T v w : ℝ) (hT : 0 ≤ T) (hv : 0 < v) (hw : 0 ≤ w) :
    (∫ t in mixedSet A D T v w, ‖D t*F t‖^2) ≤
      (w^2/v^(2*k))*(∫ t in -T..T, ‖A t^k*F t‖^2) :=
  restricted_bound k A D F hA hD hF _ (mixedSet_measurable A D hA hD T v w) T v w hT hv hw
    (fun _t ht ↦ ht.1) (fun _t ht ↦ ht.2.1) (fun _t ht ↦ ht.2.2)
end PaperP1.MixedFrequencyAmplification
