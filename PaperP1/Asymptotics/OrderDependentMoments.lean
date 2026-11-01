module

public import PaperP1.Asymptotics.OrderDependentRate
public import PaperP1.Model.FactorialBranching

/-! # Growing factorial moments with the actual second moment retained

This completes the order-dependent recurrence in T19.4 without replacing
its initial pair moment by an unproved bounded constant.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderDependentMoments

open Finset Filter PaperP1.Model PaperP1.FactorialCountMoments
  PaperP1.FactorialBranching PaperP1.OrderDependentBranching
  PaperP1.OrderDependentRate

theorem rate_mono {N r k : ℕ} {C : ℝ} (hrk : r ≤ k)
    (hh : 0 ≤ Real.log (Real.log N)) : rate C N r ≤ rate C N k := by
  have hsqrt := Real.sqrt_le_sqrt (by exact_mod_cast hrk : (r : ℝ) ≤ k)
  have hH : 0 ≤ Real.log N := Real.log_natCast_nonneg _
  have hratio : 0 ≤ Real.log N / Real.log (Real.log N) := by positivity
  have hcost := mul_le_mul_of_nonneg_right hsqrt hratio
  have hconst := constant_pos C
  unfold rate orderCost
  nlinarith

theorem recurrence {N L r k : ℕ} {C : ℝ} (hN : 3 ≤ N) (hL : 0 < L)
    (hLN : L ≤ N) (hr : 2 ≤ r) (hrk : r ≤ k)
    (hkH : (k : ℝ) ≤ Real.log N) (hh : 1 ≤ Real.log (Real.log N))
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ CriticalBandScale.upperScale * Real.log N)
    (hlogB : Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ))
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    factorialCountMoment (dyadicBlock N) L (r + 1) ≤
      Real.exp (rate C N k) * factorialCountMoment (dyadicBlock N) L r := by
  have hD : ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card = r →
      ((BranchingExceptional.badStarts N L (OldValuePrimeBudget.rawValues A L)).card : ℝ) ≤
        exception N L r := by
    intro A hA hcard
    exact finite_exception_bound (by omega) hL hLN hA hcard.le
  have hrec := factorial_succ_bound (by omega : 2 ≤ N) hL r (exception N L r) hD
  have hrH : (r : ℝ) ≤ Real.log N :=
    (by exact_mod_cast hrk : (r : ℝ) ≤ k).trans hkH
  have hsource := finite_source_rate hN hLN (by omega : 1 ≤ r) hrH hh hwidth hlogB hband
  have hcoefficient : (N : ℝ) * (2 ^ L : ℝ)⁻¹ + exception N L r ≤ Real.exp (rate C N k) := by
    calc
      _ ≤ (N : ℝ) * (2 ^ L : ℝ)⁻¹ + sourceException N L r :=
        add_le_add le_rfl (exception_le_source N L r)
      _ ≤ Real.exp (rate C N r) := hsource
      _ ≤ _ := Real.exp_le_exp.mpr (rate_mono hrk (by linarith))
  exact hrec.trans (mul_le_mul_of_nonneg_right hcoefficient
    (factorialCountMoment_nonneg (subset_refl _) r))

theorem finite_from_two {N L k : ℕ} {C : ℝ} (hN : 3 ≤ N) (hL : 0 < L)
    (hLN : L ≤ N) (hk : 2 ≤ k) (hkH : (k : ℝ) ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N))
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ CriticalBandScale.upperScale * Real.log N)
    (hlogB : Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ))
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    factorialCountMoment (dyadicBlock N) L k ≤
      factorialCountMoment (dyadicBlock N) L 2 *
        Real.exp (((k - 2 : ℕ) : ℝ) * rate C N k) := by
  have hind : ∀ d : ℕ, 2 + d ≤ k →
      factorialCountMoment (dyadicBlock N) L (2 + d) ≤
        factorialCountMoment (dyadicBlock N) L 2 * (Real.exp (rate C N k)) ^ d := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.add_zero, pow_zero, mul_one, le_refl]
    | succ d ih =>
      intro hd
      have hrec := recurrence hN hL hLN (by omega : 2 ≤ 2 + d) (by omega : 2 + d ≤ k)
        hkH hh hwidth hlogB hband
      have hprev := ih (by omega)
      calc
        _ ≤ Real.exp (rate C N k) * factorialCountMoment (dyadicBlock N) L (2 + d) :=
          by simpa only [Nat.add_assoc] using hrec
        _ ≤ Real.exp (rate C N k) *
            (factorialCountMoment (dyadicBlock N) L 2 * Real.exp (rate C N k) ^ d) :=
          mul_le_mul_of_nonneg_left hprev (Real.exp_pos _).le
        _ = _ := by rw [pow_succ]; ring
  have h := hind (k - 2) (by omega)
  have hindex : 2 + (k - 2) = k := by omega
  rw [hindex, ← Real.exp_nat_mul] at h
  exact h

theorem finite_source_exponent {N L k : ℕ} {C : ℝ} (hN : 3 ≤ N) (hL : 0 < L)
    (hLN : L ≤ N) (hk : 2 ≤ k) (hkH : (k : ℝ) ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N))
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ CriticalBandScale.upperScale * Real.log N)
    (hlogB : Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ))
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    factorialCountMoment (dyadicBlock N) L k ≤
      factorialCountMoment (dyadicBlock N) L 2 *
        Real.exp ((((k : ℝ) - 2) / 2) * Real.log N + constant C *
          ((k : ℝ) * Real.log (Real.log N) +
            (k : ℝ) * Real.sqrt k * (Real.log N / Real.log (Real.log N)))) := by
  have h := finite_from_two hN hL hLN hk hkH hh hwidth hlogB hband
  have hcost := orderCost_nonneg k (by linarith : 0 ≤ Real.log (Real.log N))
  have hconst := constant_pos C
  have hkcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by rw [Nat.cast_sub hk]; norm_num
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (factorialCountMoment_nonneg (subset_refl _) 2))
  rw [hkcast]
  unfold rate orderCost at *
  have hnonneg : 0 ≤ constant C *
      (Real.log (Real.log N) + Real.sqrt k * (Real.log N / Real.log (Real.log N))) := by
    have h := orderCost_nonneg k (by linarith : 0 ≤ Real.log (Real.log N))
    unfold orderCost at h
    positivity
  nlinarith

/-- A single threshold controls every `2 ≤ k ≤ log N`. The factor in
front is the actual second factorial moment, with no bound assumed. -/
theorem uniform_from_two (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ Real.log N →
        factorialCountMoment (dyadicBlock N) L k ≤
          factorialCountMoment (dyadicBlock N) L 2 *
            Real.exp ((((k : ℝ) - 2) / 2) * Real.log N + K *
              ((k : ℝ) * Real.log (Real.log N) +
                (k : ℝ) * Real.sqrt k * (Real.log N / Real.log (Real.log N)))) := by
  obtain ⟨N₀, hN₀, hconditions⟩ := OrderPrimeBudget.critical_conditions C
  refine ⟨constant C, constant_pos C, N₀, hN₀, ?_⟩
  intro N hN L hband k hk hkH
  obtain ⟨hLN, hh, hwidth, hlogB⟩ := hconditions N hN L hband
  have hL : 0 < L := by
    have hH : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogBpos : 0 < Real.log (L + 1 : ℕ) := by linarith
    by_contra h
    have hzero : L = 0 := by omega
    simp [hzero] at hlogBpos
  exact finite_source_exponent (by omega) hL hLN hk hkH hh hwidth hlogB hband

theorem three_half_power (k : ℕ) :
    (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) * Real.sqrt k := by
  by_cases hk : k = 0
  · simp [hk, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem uniform_source_growth (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ Real.log N →
        factorialCountMoment (dyadicBlock N) L k ≤
          factorialCountMoment (dyadicBlock N) L 2 *
            Real.exp ((((k : ℝ) - 2) / 2) * Real.log N + K *
              ((k : ℝ) * Real.log (Real.log N) +
                (k : ℝ) ^ (3 / 2 : ℝ) * (Real.log N / Real.log (Real.log N)))) := by
  simpa only [three_half_power] using uniform_from_two C

end PaperP1.OrderDependentMoments
