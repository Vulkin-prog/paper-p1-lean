module

public import PaperP1.Asymptotics.OrderDependentMoments
public import PaperP1.Asymptotics.BoundedSecondMoment

/-! # The complete unconditional growing-order moment bound

The branching construction, recurrence and bounded second-moment seed are all
internally proved. The exponential constant is chosen before N,L and k.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderDependentMomentBound

open PaperP1.Model PaperP1.FactorialCountMoments

theorem uniform_source_growth (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ Real.log N →
        factorialCountMoment (dyadicBlock N) L k ≤
          Real.exp ((((k : ℝ) - 2) / 2) * Real.log N + K *
            ((k : ℝ) * Real.log (Real.log N) +
              (k : ℝ) ^ (3 / 2 : ℝ) * (Real.log N / Real.log (Real.log N)))) := by
  obtain ⟨K, hK, NM, hNM, hgrowth⟩ := OrderDependentMoments.uniform_source_growth C
  obtain ⟨NG, hNG, hconditions⟩ := OrderPrimeBudget.critical_conditions C
  let A := BoundedSecondMoment.seedConstant C
  have hAone : 1 < A := BoundedSecondMoment.seedConstant_gt_one C
  have hA : 0 < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hAone.le
  obtain ⟨NS, _hNS, hseed⟩ := BoundedSecondMoment.uniform_bound C
  refine ⟨K + Real.log A + 1, by linarith, max NM (max NS NG), by omega, ?_⟩
  intro N hN L hband k hk hkH
  have hgrow := hgrowth N (by omega) L hband k hk hkH
  have hsecond : factorialCountMoment (dyadicBlock N) L 2 ≤ A :=
    hseed N (by omega) L hband
  have hh := (hconditions N (by omega) L hband).2.1
  have hH : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnonneg : 0 ≤ (k : ℝ) ^ (3 / 2 : ℝ) *
      (Real.log N / Real.log (Real.log N)) := by positivity
  have hkh := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hcost : 1 ≤ (k : ℝ) * Real.log (Real.log N) +
      (k : ℝ) ^ (3 / 2 : ℝ) * (Real.log N / Real.log (Real.log N)) := by
    nlinarith only [hkreal, hkh, hnonneg]
  have habsorb := mul_le_mul_of_nonneg_left hcost
    (by linarith : 0 ≤ Real.log A + 1)
  calc
    _ ≤ A * Real.exp ((((k : ℝ) - 2) / 2) * Real.log N + K *
          ((k : ℝ) * Real.log (Real.log N) +
            (k : ℝ) ^ (3 / 2 : ℝ) * (Real.log N / Real.log (Real.log N)))) :=
      hgrow.trans (mul_le_mul_of_nonneg_right hsecond (Real.exp_pos _).le)
    _ = Real.exp (Real.log A + ((((k : ℝ) - 2) / 2) * Real.log N + K *
          ((k : ℝ) * Real.log (Real.log N) +
            (k : ℝ) ^ (3 / 2 : ℝ) * (Real.log N / Real.log (Real.log N))))) := by
      rw [Real.exp_add (Real.log A), Real.exp_log hA]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [habsorb])

end PaperP1.OrderDependentMomentBound
