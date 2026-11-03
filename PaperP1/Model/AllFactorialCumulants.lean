module

public import PaperP1.Algebra.FormalFactorialCumulants
public import PaperP1.Model.TouchardCountMoments
public import PaperP1.Model.RegularCumulantTransfer
public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Model.HeterogeneousDirectMaximum

/-! # Every actual count factorial cumulant is the corresponding coefficient of the formal logarithm of its factorial generating series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllFactorialCumulants

open Finset PowerSeries PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum

def series (G : Finset ℕ) (L : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk fun r ↦ factorialCountMoment G L r / (r.factorial : ℝ)

def factorialCumulant (G : Finset ℕ) (L r : ℕ) : ℝ :=
  FormalFactorialCumulants.cumulant (series G L) r

theorem moment_series (G : Finset ℕ) (L r : ℕ) :
    FormalFactorialCumulants.moment (series G L) r = factorialCountMoment G L r := by
  rw [FormalFactorialCumulants.moment, series, PowerSeries.coeff_mk]
  exact mul_div_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero r)

theorem series_coeff {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (r : ℕ) :
    PowerSeries.coeff r (series G L) = ∑ I ∈ G.powersetCard r, infiniteJointMoment L I := by
  rw [series, PowerSeries.coeff_mk, factorialCountMoment_eq_subset hG r]
  have hfac : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  field_simp

theorem series_constant {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    PowerSeries.constantCoeff (series G L) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, series_coeff hG 0]
  simp only [powersetCard_zero, sum_singleton, infiniteJointMoment_empty]

theorem recurrence {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (n : ℕ) :
    factorialCumulant G L (n + 1) = factorialCountMoment G L (n + 1) -
      ∑ i ∈ range n, (n.choose i : ℝ) * factorialCumulant G L (i + 1) * factorialCountMoment G L (n - i) := by
  simpa only [factorialCumulant, moment_series] using
    FormalFactorialCumulants.recurrence (series G L) (series_constant hG) n

theorem cumulant_zero {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) : factorialCumulant G L 0 = 0 :=
  FormalFactorialCumulants.cumulant_zero (series G L) (series_constant hG)

theorem cumulant_one {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    factorialCumulant G L 1 = actualMean G L := by
  rw [factorialCumulant, FormalFactorialCumulants.cumulant_one _ (series_constant hG), moment_series,
    factorialCountMoment_one, countMoment_one hG]
  rfl

theorem cumulant_two {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    factorialCumulant G L 2 = RegularCumulantTransfer.secondFactorialCumulant G L := by
  rw [factorialCumulant, FormalFactorialCumulants.cumulant_two _ (series_constant hG), moment_series,
    moment_series, factorialCountMoment_two hG, factorialCountMoment_one]
  rfl

theorem cumulant_three {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    factorialCumulant G L 3 = ThirdRunFactorialCumulant.thirdFactorialCumulant G L := by
  rw [factorialCumulant, FormalFactorialCumulants.cumulant_three _ (series_constant hG)]
  simp only [moment_series, ThirdRunFactorialCumulant.thirdFactorialCumulant]

theorem cumulant_four {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    factorialCumulant G L 4 = FourthRunFactorialCumulant.fourthFactorialCumulant G L := by
  rw [factorialCumulant, FormalFactorialCumulants.cumulant_four _ (series_constant hG)]
  simp only [moment_series, FourthRunFactorialCumulant.fourthFactorialCumulant]

end PaperP1.AllFactorialCumulants
