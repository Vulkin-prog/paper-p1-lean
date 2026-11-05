module

public import PaperP1.Arithmetic.DegreeUniformPlanePresentation
public import PaperP1.Diophantine.PolynomialPrimeAffineCount
public import PaperP1.Analysis.AffineDeterminantUniformScale
public import Mathlib.Data.Nat.Log

/-! # Explicit parameters for a weaker degree-uniform affine estimate

These choices give polynomial degree dependence. They do not assert the sharp
quadratic degree dependence required by the original BCN consequence.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeUniformAffineParameters

open Polynomial BivariateDegrees BivariateHeight

def logarithmicBudget (N : ℕ) : ℕ := Nat.log2 N + 1

def avoidanceCount (D N : ℕ) : ℕ := 64 * D ^ 3 * logarithmicBudget N + 1

def auxiliaryDegree (N : ℕ) : ℕ := 3 * logarithmicBudget N + 1

theorem box_le_cubic (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N) :
    (D + 1) * N ≤ N ^ 3 := by
  have hN : 2 ≤ N := hD.trans hDN
  have hm : 2 * N ≤ N * N := Nat.mul_le_mul_right N hN
  have hp : D + 1 ≤ N ^ 2 := by nlinarith
  calc
    _ ≤ N ^ 2 * N := Nat.mul_le_mul_right N hp
    _ = _ := by ring

theorem obstruction_nat (D N a h : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (ha : a ≤ D) (hh : h ≤ N ^ (32 * D ^ 3)) :
    (a + 1) * (D + 1) * D * h * ((D + 1) * N) ^ (a + 1) *
      ((D + 1) * N) ^ D ≤ N ^ (64 * D ^ 3) := by
  have hN : 2 ≤ N := hD.trans hDN
  have hN1 : 1 ≤ N := by omega
  have hm : 2 * N ≤ N * N := Nat.mul_le_mul_right N hN
  have hplus : D + 1 ≤ N ^ 2 := by nlinarith
  have haplus : a + 1 ≤ N ^ 2 := (Nat.add_le_add_right ha 1).trans hplus
  have hcoef : (a + 1) * (D + 1) * D ≤ N ^ 5 := by
    calc
      _ ≤ N ^ 2 * N ^ 2 * N := Nat.mul_le_mul (Nat.mul_le_mul haplus hplus) hDN
      _ = _ := by ring
  have hbox := box_le_cubic D N hD hDN
  have hpows : ((D + 1) * N) ^ (a + 1) * ((D + 1) * N) ^ D ≤ N ^ (6 * D + 3) := by
    calc
      _ ≤ (N ^ 3) ^ (a + 1) * (N ^ 3) ^ D :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hbox _) (Nat.pow_le_pow_left hbox _)
      _ = N ^ (3 * (a + 1) + 3 * D) := by rw [← pow_mul, ← pow_mul, ← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hN1 (by omega)
  have hDcube : D ≤ D ^ 3 := Nat.le_self_pow (by decide) D
  have hcube : 8 ≤ D ^ 3 := by simpa using Nat.pow_le_pow_left hD 3
  have he : 5 + 32 * D ^ 3 + (6 * D + 3) ≤ 64 * D ^ 3 := by omega
  calc
    _ = ((a + 1) * (D + 1) * D) * h *
        (((D + 1) * N) ^ (a + 1) * ((D + 1) * N) ^ D) := by ring
    _ ≤ N ^ 5 * N ^ (32 * D ^ 3) * N ^ (6 * D + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul hcoef hh) hpows
    _ = N ^ (5 + 32 * D ^ 3 + (6 * D + 3)) := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right hN1 he

theorem obstruction_real (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N)
    (G : ℤ[X][X]) (ha : degreeX G ≤ D) (hb : degreeY G = D)
    (hh : height G ≤ N ^ (32 * D ^ 3)) :
    (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      (((D + 1) * N : ℕ) : ℝ) ^ (degreeX G + 1) *
      (((D + 1) * N : ℕ) : ℝ) ^ degreeY G ≤ ((N ^ (64 * D ^ 3) : ℕ) : ℝ) := by
  rw [hb]
  exact_mod_cast obstruction_nat D N (degreeX G) (height G) hD hDN ha hh

theorem binary_upper (N : ℕ) : N < 2 ^ logarithmicBudget N := by
  simpa only [logarithmicBudget, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) N

theorem log_le_budget (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N : ℝ) ≤ logarithmicBudget N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ logarithmicBudget N := by
    exact_mod_cast (binary_upper N).le
  have hh := Real.log_le_log hpos hpow
  rw [Real.log_pow] at hh
  have htwo : Real.log 2 ≤ 1 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) (logarithmicBudget N)))

theorem obstruction_lt_prime_power (D N P : ℕ) (hP : 2 ≤ P) :
    N ^ (64 * D ^ 3) < P ^ avoidanceCount D N := by
  have hpos : 0 < 2 ^ (logarithmicBudget N * (64 * D ^ 3)) := by positivity
  calc
    _ ≤ (2 ^ logarithmicBudget N) ^ (64 * D ^ 3) :=
      Nat.pow_le_pow_left (binary_upper N).le _
    _ = 2 ^ (logarithmicBudget N * (64 * D ^ 3)) := (pow_mul _ _ _).symm
    _ < 2 ^ (logarithmicBudget N * (64 * D ^ 3) + 1) := by
      rw [pow_succ (2 : ℕ) (logarithmicBudget N * (64 * D ^ 3))]
      omega
    _ = 2 ^ avoidanceCount D N := by congr 1; unfold avoidanceCount; ring
    _ ≤ _ := Nat.pow_le_pow_left hP _

theorem avoidance_le (D N : ℕ) (hD : 2 ≤ D) :
    avoidanceCount D N ≤ 128 * D ^ 3 * logarithmicBudget N := by
  have hcube : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hL : 1 ≤ logarithmicBudget N := by unfold logarithmicBudget; omega
  have hm : 1 ≤ D ^ 3 * logarithmicBudget N := by
    exact (by norm_num : 1 = 1 * 1).trans_le (Nat.mul_le_mul hcube hL)
  unfold avoidanceCount
  nlinarith

theorem auxiliary_budget (D N : ℕ) (hD : 2 ≤ D) (hDN : D ≤ N) :
    1 ≤ auxiliaryDegree N ∧
      Real.log (((D + 1) * N : ℕ) : ℝ) ≤ (auxiliaryDegree N : ℝ) + 1 ∧
      auxiliaryDegree N + (D - 1) ≤ 4 * D * logarithmicBudget N := by
  have hN : 1 ≤ N := by omega
  have hL : 1 ≤ logarithmicBudget N := by unfold logarithmicBudget; omega
  have hbox : (((D + 1) * N : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 := by
    exact_mod_cast box_le_cubic D N hD hDN
  have hboxpos : (0 : ℝ) < (((D + 1) * N : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hboxpos hbox
  rw [Real.log_pow] at hlog
  push_cast at hlog
  have hNlog := log_le_budget N hN
  refine ⟨by unfold auxiliaryDegree; omega, ?_, ?_⟩
  · unfold auxiliaryDegree
    push_cast
    linarith
  · have hm : D ≤ D * logarithmicBudget N := Nat.le_mul_of_pos_right D (by omega)
    have h3 : 3 * logarithmicBudget N ≤ 3 * D * logarithmicBudget N := by nlinarith
    unfold auxiliaryDegree
    have hpred : D - 1 + 1 = D := by omega
    nlinarith

end PaperP1.DegreeUniformAffineParameters
