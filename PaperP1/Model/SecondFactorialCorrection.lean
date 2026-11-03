module

public import PaperP1.Model.FactorialCountMoments
public import PaperP1.Model.HeterogeneousRunConversion
public import PaperP1.Model.RetainedReferenceTheorem
public import PaperP1.Arithmetic.FiniteChannelHierarchy

/-! # The literal nominal second factorial correction and the actual regular covariance parameter -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondFactorialCorrection

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.FactorialCountMoments PaperP1.FiniteChannelHierarchy

def value (N L : ℕ) : ℝ := factorialCountMoment (dyadicBlock N) L 2 - nominalMean N L ^ 2

def regularCovariance (N L : ℕ) : ℝ :=
  ∑ e ∈ (RegularStarts.regularStarts N L).powersetCard 2, infiniteCenteredCoefficient L e

theorem gap_identity (N L : ℕ) :
    value N L - RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L =
      countMoment (dyadicBlock N) L 1 ^ 2 - nominalMean N L ^ 2 := by
  rw [value, factorialCountMoment_two Subset.rfl, RegularCumulantTransfer.secondFactorialCumulant]
  ring

theorem regular_mean {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    countMoment (RegularStarts.regularStarts N L) L 1 =
      ((RegularStarts.regularStarts N L).card : ℝ) * (2 ^ L : ℝ)⁻¹ := by
  rw [countMoment_one (RegularStarts.regularStarts_subset N L)]
  calc
    _ = ∑ _x ∈ RegularStarts.regularStarts N L, (2 ^ L : ℝ)⁻¹ :=
      sum_congr rfl (fun x hx ↦ RetainedReferenceTheorem.ground_marginal hN hL x hx)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem regular_cumulant {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    RegularCumulantTransfer.secondFactorialCumulant (RegularStarts.regularStarts N L) L =
      2 * regularCovariance N L - ((RegularStarts.regularStarts N L).card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  rw [HeterogeneousRunConversion.second_cumulant_formula (RegularStarts.regularStarts_subset N L)]
  congr 1
  change (∑ x ∈ RegularStarts.regularStarts N L, infiniteMarginal x L ^ 2) = _
  calc
    _ = ∑ _x ∈ RegularStarts.regularStarts N L, ((2 ^ L : ℝ)⁻¹) ^ 2 :=
      sum_congr rfl (fun x hx ↦ congrArg (fun p : ℝ ↦ p ^ 2) (RetainedReferenceTheorem.ground_marginal hN hL x hx))
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end PaperP1.SecondFactorialCorrection
