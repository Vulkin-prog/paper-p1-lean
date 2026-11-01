module

public import PaperP1.Asymptotics.ShortSplitMoments
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Measurability and actual Lp norms of finite split-product sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitSumLp

open scoped ENNReal

open Finset MeasureTheory PaperP1.Model PaperP1.SplitOffsetProducts PaperP1.ShortSplitMoments
open PaperP1.Model.InfiniteRademacher PaperP1.Probability.CylinderExpectations
open PaperP1.Probability.InfiniteCylinderTransfer

local instance : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

theorem sumValue_aestronglyMeasurable (A : Finset ℤ) (S : Finset ℕ) :
    AEStronglyMeasurable (sumValue A S) infiniteRademacherMeasure := by
  classical
  let M := S.sup fun n ↦ product A n
  let F : SampleSpace M → ℝ := fun σ ↦ ∑ n ∈ S, (randomMultiplicativeValue σ (product A n) : ℝ)
  have hobs : sumValue A S = F ∘ restrictToFinite M := by
    funext ω
    apply sum_congr rfl
    intro n hn
    rw [randomMultiplicativeValue_restrictToFinite_eq_infiniteRandomValue ω (le_sup hn)]
  rw [hobs]
  have hF := (PaperP1.Probability.integrable_finite_function (infiniteRademacherMeasure.map (restrictToFinite M)) F).aestronglyMeasurable
  exact hF.comp_aemeasurable (measurable_restrictToFinite M).aemeasurable

theorem sumValue_bound (A : Finset ℤ) (S : Finset ℕ) (ω : InfiniteSample) :
    ‖sumValue A S ω‖ ≤ S.card := by
  have hval : ∀ n : ℕ, |(infiniteRandomValue ω (product A n) : ℝ)| = 1 := by
    intro n
    unfold infiniteRandomValue phase
    split_ifs <;> norm_num
  rw [Real.norm_eq_abs]
  unfold sumValue
  calc
    _ ≤ ∑ n ∈ S, |(infiniteRandomValue ω (product A n) : ℝ)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [hval, sum_const, nsmul_eq_mul, mul_one]

theorem sumValue_memLp (A : Finset ℤ) (S : Finset ℕ) (p : ℝ≥0∞) :
    MemLp (sumValue A S) p infiniteRademacherMeasure :=
  MemLp.of_bound (sumValue_aestronglyMeasurable A S) S.card
    (Filter.Eventually.of_forall (sumValue_bound A S))

theorem lpNorm_eq_moment (A : Finset ℤ) (S : Finset ℕ) (v : ℕ) (hv : 0 < v) :
    lpNorm (sumValue A S) (v : ℝ≥0∞) infiniteRademacherMeasure =
      (∫ ω, |sumValue A S ω| ^ v ∂infiniteRademacherMeasure) ^ (1 / (v : ℝ)) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hv.ne') (by simp)
    (sumValue_aestronglyMeasurable A S)]
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, Real.rpow_natCast, one_div]

end PaperP1.SplitSumLp
