module

public import PaperP1.Asymptotics.OrderPrimeBudget
public import PaperP1.Asymptotics.QuadraticOrderMoments

/-! # The first uniform growing-order rate in companion T19.4 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderDependentRate

open Finset Filter PaperP1.Model PaperP1.CriticalBandScale
  PaperP1.OrderDependentBranching

def primeConstant : ℝ :=
  PrimeCardinalityEuler.constant * Real.sqrt (2 * OrderPrimeBudget.coefficient)

def prefactor (C : ℝ) : ℝ := |Real.log upperScale| + Real.log 2 + Real.log 3 +
  |C| * Real.log 2 + 3

def constant (C : ℝ) : ℝ := prefactor C + primeConstant + Real.log 3 + 1

def orderCost (N j : ℕ) : ℝ :=
  Real.sqrt j * (Real.log N / Real.log (Real.log N))

def rate (C : ℝ) (N j : ℕ) : ℝ :=
  Real.log N / 2 + constant C * (Real.log (Real.log N) + orderCost N j)

theorem primeConstant_nonneg : 0 ≤ primeConstant := by
  unfold primeConstant
  have h := PrimeCardinalityEuler.constant_pos
  positivity

theorem prefactor_bounds (C : ℝ) :
    0 ≤ prefactor C ∧ |Real.log upperScale| + Real.log 2 + 2 ≤ prefactor C ∧
      |Real.log upperScale| + Real.log 3 / 2 + 1 ≤ prefactor C ∧
      |C| * Real.log 2 ≤ prefactor C := by
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have habs := abs_nonneg (Real.log upperScale)
  have hC := mul_nonneg (abs_nonneg C) htwo
  unfold prefactor
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem constant_pos (C : ℝ) : 0 < constant C := by
  have hA := (prefactor_bounds C).1
  have hQ := primeConstant_nonneg
  have hthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  unfold constant
  positivity

theorem orderCost_nonneg {N : ℕ} (j : ℕ)
    (hh : 0 ≤ Real.log (Real.log N)) : 0 ≤ orderCost N j := by
  have hH : 0 ≤ Real.log N := Real.log_natCast_nonneg _
  unfold orderCost
  positivity

theorem finite_source_rate {N L j : ℕ} {C : ℝ} (hN : 3 ≤ N)
    (hLN : L ≤ N) (hj : 1 ≤ j) (hjH : (j : ℝ) ≤ Real.log N)
    (hh : 1 ≤ Real.log (Real.log N))
    (hwidth : ((L + 1 : ℕ) : ℝ) ≤ upperScale * Real.log N)
    (hlogB : Real.log (Real.log N) / 2 ≤ Real.log (L + 1 : ℕ))
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (N : ℝ) * (2 ^ L : ℝ)⁻¹ + sourceException N L j ≤ Real.exp (rate C N j) := by
  have hH : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh0 : 0 < Real.log (Real.log N) := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hu := upperScale_pos
  have hQ := primeConstant_nonneg
  have hcost := orderCost_nonneg j hh0.le
  obtain ⟨hA, hAc, hAp, hAm⟩ := prefactor_bounds C
  let E := Real.log N / 2 + prefactor C * Real.log (Real.log N) +
    primeConstant * orderCost N j
  have hAe : prefactor C * Real.log (Real.log N) ≤ E := by
    dsimp only [E]
    have h := mul_nonneg hQ hcost
    linarith
  have hB : ((L + 1 : ℕ) : ℝ) ≤
      Real.exp (|Real.log upperScale| + Real.log (Real.log N)) := by
    calc
      _ ≤ upperScale * Real.log N := hwidth
      _ = Real.exp (Real.log upperScale + Real.log (Real.log N)) := by
        rw [Real.exp_add, Real.exp_log hu, Real.exp_log hH]
      _ ≤ _ := Real.exp_le_exp.mpr (add_le_add (le_abs_self _) le_rfl)
  have hrootN : Real.sqrt (3 * N : ℕ) =
      Real.exp (Real.log N / 2 + Real.log 3 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (3 * N : ℕ))]
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hn.ne']
    congr 1
    ring
  have hroot := OrderPrimeBudget.finite_root_bound hN hLN hj hh hwidth hlogB
  have hexponent : exponent N L j ≤ primeConstant * orderCost N j := by
    have h := mul_le_mul_of_nonneg_left hroot PrimeCardinalityEuler.constant_pos.le
    simpa only [exponent, primeConstant, orderCost, mul_assoc] using h
  have hpool : ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
      Real.exp (exponent N L j) ≤ Real.exp E := by
    rw [hrootN]
    calc
      _ ≤ Real.exp (|Real.log upperScale| + Real.log (Real.log N)) *
          Real.exp (Real.log N / 2 + Real.log 3 / 2) *
          Real.exp (primeConstant * orderCost N j) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le)
          (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le (by positivity)
      _ ≤ Real.exp E := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hconst := mul_le_mul_of_nonneg_left hh
          (show 0 ≤ |Real.log upperScale| + Real.log 3 / 2 by positivity)
        have hcoef := mul_le_mul_of_nonneg_right hAp hh0.le
        dsimp [E]
        nlinarith
  have hcontact : (j : ℝ) * (2 * L + 1) ≤ Real.exp E := by
    have hcontact0 : (j : ℝ) * (2 * L + 1) ≤ 2 * upperScale * (Real.log N) ^ 2 := by
      have hB : (2 : ℝ) * L + 1 ≤ 2 * upperScale * Real.log N := by
        push_cast at hwidth
        linarith
      have h := mul_le_mul hjH hB (by positivity : (0 : ℝ) ≤ 2 * L + 1) hH.le
      nlinarith
    have hcontactE : 2 * upperScale * (Real.log N) ^ 2 ≤
        Real.exp ((|Real.log upperScale| + Real.log 2 + 2) * Real.log (Real.log N)) := by
      calc
        _ = Real.exp (Real.log 2 + Real.log upperScale + 2 * Real.log (Real.log N)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2),
            Real.exp_log hu, show (2 : ℝ) * Real.log (Real.log N) =
              (2 : ℕ) * Real.log (Real.log N) by norm_num, Real.exp_nat_mul, Real.exp_log hH]
        _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          have hconstant := mul_le_mul_of_nonneg_left hh
            (show 0 ≤ |Real.log upperScale| + Real.log 2 by positivity)
          nlinarith [le_abs_self (Real.log upperScale)]
    exact hcontact0.trans (hcontactE.trans (Real.exp_le_exp.mpr
      ((mul_le_mul_of_nonneg_right hAc hh0.le).trans hAe)))
  have hmean : (N : ℝ) * (2 ^ L : ℝ)⁻¹ ≤ Real.exp E := by
    calc
      _ ≤ (2 : ℝ) ^ C := QuadraticOrderMoments.nominal_mean_bound (by omega) hband
      _ = Real.exp (C * Real.log 2) := by rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      _ ≤ Real.exp E := by
        apply Real.exp_le_exp.mpr
        have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hC := mul_le_mul_of_nonneg_right (le_abs_self C) htwo
        have hC' := mul_le_mul_of_nonneg_left hh (mul_nonneg (abs_nonneg C) htwo)
        have hC'' := mul_le_mul_of_nonneg_right hAm hh0.le
        linarith
  have hsum : (N : ℝ) * (2 ^ L : ℝ)⁻¹ + sourceException N L j ≤ 3 * Real.exp E := by
    unfold sourceException
    linarith
  refine hsum.trans ?_
  rw [show 3 * Real.exp E = Real.exp (Real.log 3 + E) by
    symm; rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]]
  apply Real.exp_le_exp.mpr
  have hthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hthree' := mul_le_mul_of_nonneg_left hh hthree
  have hK1 : prefactor C + Real.log 3 ≤ constant C := by unfold constant; linarith
  have hK2 : primeConstant ≤ constant C := by unfold constant; linarith
  have h1 := mul_le_mul_of_nonneg_right hK1 hh0.le
  have h2 := mul_le_mul_of_nonneg_right hK2 hcost
  unfold rate
  dsimp [E]
  nlinarith

/-- The literal source logarithmic estimate, with one threshold preceding
all orders `1 ≤ j ≤ log N`, all critical lengths, and all exposed windows. -/
theorem uniform_source_rate (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ Real.log N →
        Real.log ((N : ℝ) * (2 ^ L : ℝ)⁻¹ + sourceException N L j) ≤
          Real.log N / 2 + K * (Real.log (Real.log N) +
            Real.sqrt j * (Real.log N / Real.log (Real.log N))) := by
  obtain ⟨N₀, hN₀, hconditions⟩ := OrderPrimeBudget.critical_conditions C
  refine ⟨constant C, constant_pos C, N₀, hN₀, ?_⟩
  intro N hN L hband j hj hjH
  obtain ⟨hLN, hh, hwidth, hlogB⟩ := hconditions N hN L hband
  have hbound := finite_source_rate (by omega) hLN hj hjH hh hwidth hlogB hband
  have hpos : 0 < (N : ℝ) * (2 ^ L : ℝ)⁻¹ + sourceException N L j := by
    unfold sourceException
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  have h := Real.log_le_log hpos hbound
  simpa only [Real.log_exp, rate, orderCost] using h

end PaperP1.OrderDependentRate
