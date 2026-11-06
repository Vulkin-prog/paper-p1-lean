module

public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.FiniteFibreSquareBudget
public import PaperP1.Analysis.NarrowCofactorMeanValue

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmallPrimeRegion
open Finset PaperP1 MeasureTheory
open scoped Classical

def goodSet (H : ℕ) (P : Finset ℕ) (f : ℕ → ℂ) (T V : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc (-T) T ∧ ∀ j ∈ NarrowPrimeBands.indices H P,
    ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f t‖ ≤ V}

theorem finite_product_bound {ι : Type*} (J : Finset ι) (A F : ι → ℝ → ℂ)
    (hA : ∀ j ∈ J, Continuous (A j)) (hF : ∀ j ∈ J, Continuous (F j))
    (E : Set ℝ) (hE : MeasurableSet E) (T V C : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hsub : E ⊆ Set.Ioc (-T) T) (hsmall : ∀ t ∈ E, ∀ j ∈ J, ‖A j t‖ ≤ V)
    (hmean : ∀ j ∈ J, (∫ t in -T..T, ‖F j t‖^2) ≤ C) :
    (∫ t in E, ‖∑ j ∈ J, A j t*F j t‖^2) ≤ (J.card : ℝ)^2*V^2*C := by
  have hS : Continuous (fun t ↦ ‖∑ j ∈ J, A j t*F j t‖^2) :=
    (continuous_finsetSum J (fun j hj ↦ (hA j hj).mul (hF j hj))).norm.pow 2
  have hG : Continuous (fun t ↦ (J.card : ℝ)*V^2*(∑ j ∈ J, ‖F j t‖^2)) := by
    apply continuous_const.mul
    exact continuous_finsetSum J (fun j hj ↦ (hF j hj).norm.pow 2)
  have hpoint (t : ℝ) (ht : t ∈ E) :
      ‖∑ j ∈ J, A j t*F j t‖^2 ≤ (J.card : ℝ)*V^2*(∑ j ∈ J, ‖F j t‖^2) := by
    have hs : (∑ j ∈ J, ‖A j t*F j t‖^2) ≤ V^2*(∑ j ∈ J, ‖F j t‖^2) := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      rw [norm_mul,mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hV).mpr (hsmall t ht j hj)) (sq_nonneg _)
    exact (FiniteFibreSquareBudget.norm_sum_sq_le_card J (fun j ↦ A j t*F j t)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg J.card : (0 : ℝ) ≤ J.card))
  have hi := setIntegral_mono_on (μ := volume) ((hS.intervalIntegrable (-T) T).1.mono_set hsub)
    ((hG.intervalIntegrable (-T) T).1.mono_set hsub) hE hpoint
  have he := setIntegral_mono_set (μ := volume) (hG.intervalIntegrable (-T) T).1
    (Filter.Eventually.of_forall (fun t ↦ by positivity : ∀ t : ℝ, 0 ≤ (J.card : ℝ)*V^2*(∑ j ∈ J, ‖F j t‖^2)))
    (Filter.Eventually.of_forall hsub)
  have hsum : (∑ j ∈ J, ∫ t in Set.Ioc (-T) T, ‖F j t‖^2) ≤ (J.card : ℝ)*C := by
    calc
      _ ≤ ∑ _j ∈ J, C := sum_le_sum (fun j hj ↦ by
        rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
        exact hmean j hj)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hwhole : (∫ t in Set.Ioc (-T) T, (J.card : ℝ)*V^2*(∑ j ∈ J, ‖F j t‖^2)) ≤
      (J.card : ℝ)^2*V^2*C := by
    have hfi : ∀ j ∈ J, IntegrableOn (fun t ↦ ‖F j t‖^2) (Set.Ioc (-T) T) :=
      fun j hj ↦ ((hF j hj).norm.pow 2).intervalIntegrable (-T) T |>.1
    rw [integral_const_mul,integral_finsetSum J (f := fun j t ↦ ‖F j t‖^2) hfi]
    have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (J.card : ℝ)*V^2)
    exact hh.trans_eq (by ring)
  exact hi.trans (he.trans hwhole)

theorem rectangle_bound (X H : ℕ) (hX : 0 < X) (P Q : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ Icc 1 (2*X), ‖f n‖ ≤ 1) (E : Set ℝ) (hE : MeasurableSet E)
    (T h V : ℝ) (hT : 0 < T) (hh : 0 < h) (hTh : T ≤ (X : ℝ)/h) (hV : 0 ≤ V)
    (hanchor : ∀ j ∈ NarrowPrimeBands.indices H P, NarrowPrimeBands.anchor H j ≤ h)
    (hsub : E ⊆ Set.Ioc (-T) T)
    (hsmall : ∀ t ∈ E, ∀ j ∈ NarrowPrimeBands.indices H P,
      ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f t‖ ≤ V) :
    (∫ t in E, ‖NarrowRamareRectangle.rectangle X H P Q f t‖^2) ≤
      ((NarrowPrimeBands.indices H P).card : ℝ)^2*V^2*(2*SupportedCoefficientSquareBudget.constant) := by
  apply finite_product_bound (NarrowPrimeBands.indices H P)
    (fun j ↦ DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f)
    (fun j ↦ DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
      (NarrowRamareRectangle.coefficient P Q f))
    (fun j hj ↦ GaussianExponentialSums.polynomial_continuous _ _ _)
    (fun j hj ↦ GaussianExponentialSums.polynomial_continuous _ _ _) E hE T V _ hT.le hV hsub hsmall
  intro j hj
  exact NarrowCofactorMeanValue.short_height_bound X H j hX P Q f
    (fun n hn ↦ hf n (mem_filter.mp hn).1) T h hT hh hTh (hanchor j hj)

theorem goodSet_measurable (H : ℕ) (P : Finset ℕ) (f : ℕ → ℂ) (T V : ℝ) :
    MeasurableSet (goodSet H P f T V) := by
  have hc : IsClosed {t : ℝ | ∀ j ∈ NarrowPrimeBands.indices H P,
      ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f t‖ ≤ V} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hj
    exact isClosed_le (GaussianExponentialSums.polynomial_continuous _ _ _ |>.norm) continuous_const
  exact measurableSet_Ioc.inter hc.measurableSet

theorem goodSet_bound (X H : ℕ) (hX : 0 < X) (P Q : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ Icc 1 (2*X), ‖f n‖ ≤ 1) (T h V : ℝ) (hT : 0 < T) (hh : 0 < h)
    (hTh : T ≤ (X : ℝ)/h) (hV : 0 ≤ V)
    (hanchor : ∀ j ∈ NarrowPrimeBands.indices H P, NarrowPrimeBands.anchor H j ≤ h) :
    (∫ t in goodSet H P f T V, ‖NarrowRamareRectangle.rectangle X H P Q f t‖^2) ≤
      ((NarrowPrimeBands.indices H P).card : ℝ)^2*V^2*(2*SupportedCoefficientSquareBudget.constant) :=
  rectangle_bound X H hX P Q f hf _ (goodSet_measurable H P f T V) T h V hT hh hTh hV hanchor
    (fun _t ht ↦ ht.1) (fun _t ht ↦ ht.2)
end PaperP1.SmallPrimeRegion
