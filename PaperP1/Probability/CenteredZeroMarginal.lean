module

public import PaperP1.Probability.AdmissibleIndices

/-! # A zero actual marginal kills every centered product containing its site

Zero-weight samples remain allowed. The other centering parameters can be
arbitrary; only the zero coordinate is required to have its actual center.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CenteredZeroMarginal

open Finset PaperP1.Algebra PaperP1.Probability

theorem finite_centered_zero {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (P : FiniteProbability Ω) (J : ι → Ω → Bool) (p : ι → ℝ) (I : Finset ι)
    (x : ι) (hx : x ∈ I) (hp : exactMarginal P J x = 0) (hcenter : p x = 0) :
    centeredMoment P.weight (fun y ω ↦ (indicatorValue (J y ω) : ℝ)) p I = 0 := by
  unfold centeredMoment finiteExpectation
  apply sum_eq_zero
  intro ω _
  change P.weight ω * (∏ y ∈ I, ((indicatorValue (J y ω) : ℝ) - p y)) = 0
  by_cases hw : P.weight ω = 0
  · rw [hw, zero_mul]
  · have hwpos : 0 < P.weight ω := lt_of_le_of_ne (P.weight_nonneg ω) (Ne.symm hw)
    have hJ : J x ω = false := by
      cases heq : J x ω with
      | false => rfl
      | true =>
        have hpos := positive_marginal_of_positive_weight P J x ω hwpos heq
        rw [hp] at hpos
        exact False.elim (lt_irrefl _ hpos)
    have hprod : (∏ y ∈ I, ((indicatorValue (J y ω) : ℝ) - p y)) = 0 :=
      prod_eq_zero_iff.mpr ⟨x, hx, by simp [hJ, indicatorValue, hcenter]⟩
    rw [hprod, mul_zero]

end PaperP1.CenteredZeroMarginal
