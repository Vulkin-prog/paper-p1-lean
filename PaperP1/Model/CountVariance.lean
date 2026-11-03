module

public import PaperP1.Model.RegularCumulantTransfer
public import Mathlib.Probability.Moments.Variance

/-! # The actual infinite-model factorial cumulant is variance minus mean -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CountVariance

open MeasureTheory ProbabilityTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.CountObservables PaperP1.Probability

local instance : MeasurableSpace PaperP1.Arithmetic.F₂ := ⊤

theorem count_memLp_two (G : Finset ℕ) (L : ℕ) :
    MemLp (fun ω ↦ (infiniteStartCount G L ω : ℝ)) 2 infiniteRademacherMeasure := by
  have hm : Measurable (fun ω ↦ (infiniteStartCount G L ω : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_infiniteStartCount G L)
  apply memLp_of_bounded (a := 0) (b := (G.card : ℝ)) _ hm.aestronglyMeasurable 2
  exact ae_of_all _ fun ω ↦ ⟨Nat.cast_nonneg _, by
    exact_mod_cast indicatorCount_le_card G (fun x ↦ infiniteStartIndicator x L) ω⟩

theorem variance_count (G : Finset ℕ) (L : ℕ) :
    ProbabilityTheory.variance (fun ω ↦ (infiniteStartCount G L ω : ℝ)) infiniteRademacherMeasure =
      countMoment G L 2 - (countMoment G L 1) ^ 2 := by
  simpa only [countMoment, pow_one, Pi.pow_apply] using
    ProbabilityTheory.variance_eq_sub (count_memLp_two G L)

theorem second_cumulant_variance (G : Finset ℕ) (L : ℕ) :
    RegularCumulantTransfer.secondFactorialCumulant G L =
      ProbabilityTheory.variance (fun ω ↦ (infiniteStartCount G L ω : ℝ)) infiniteRademacherMeasure -
        ∫ ω, (infiniteStartCount G L ω : ℝ) ∂infiniteRademacherMeasure := by
  have hmean : (∫ ω, (infiniteStartCount G L ω : ℝ) ∂infiniteRademacherMeasure) = countMoment G L 1 := by
    simp only [countMoment, pow_one]
  rw [variance_count, hmean, RegularCumulantTransfer.secondFactorialCumulant]
  ring

end PaperP1.CountVariance
