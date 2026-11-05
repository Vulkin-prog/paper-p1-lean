module

public import PaperP1.Arithmetic.QuadraticRealIntegerGridCount
public import PaperP1.Arithmetic.DegreeUniformAffineParameters

/-! # An actual logarithmic order and a fixed seventeenth logarithmic power -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicQuadraticPlaneParameters

open MvPolynomial DegreeUniformAffineParameters

theorem doubling (N : ℕ) (hN : 0 < N) :
    logarithmicBudget (2 * N) = logarithmicBudget N + 1 := by
  simp only [logarithmicBudget, Nat.log2_eq_log_two]
  rw [Nat.mul_comm 2 N, Nat.log_mul_base (by decide : 1 < 2) hN.ne']

theorem quadrupling (N : ℕ) (hN : 0 < N) :
    logarithmicBudget (4 * N) = logarithmicBudget N + 2 := by
  rw [show 4 * N = 2 * (2 * N) by omega, doubling _ (by omega), doubling N hN]

theorem logarithmic_factors (N : ℕ) (hN : 0 < N) :
    ((Nat.log2 (4 * N) + 1 : ℕ) : ℝ) *
      ((logarithmicBudget (2 * N) + 1 : ℕ) : ℝ) ^ 16 ≤
      (3 : ℝ) ^ 17 * (logarithmicBudget N : ℝ) ^ 17 := by
  change (logarithmicBudget (4 * N) : ℝ) *
    ((logarithmicBudget (2 * N) + 1 : ℕ) : ℝ) ^ 16 ≤ _
  rw [quadrupling N hN, doubling N hN]
  push_cast
  have hL : (1 : ℝ) ≤ logarithmicBudget N := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hle : (logarithmicBudget N : ℝ) + 2 ≤ 3 * (logarithmicBudget N : ℝ) := by linarith only [hL]
  calc
    _ = ((logarithmicBudget N : ℝ) + 2) ^ 17 := by ring
    _ ≤ (3 * (logarithmicBudget N : ℝ)) ^ 17 := pow_le_pow_left₀ (by positivity) hle 17
    _ = _ := by rw [mul_pow]

theorem high_degree_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (N : ℕ) (hN : 0 < N) (hdegree : logarithmicBudget (2 * N) < P.totalDegree)
    (S : Finset (Fin 2 → ℤ))
    (hcurve : ∀ z ∈ S, eval (fun i ↦ (z i : ℝ)) P = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ N) :
    (S.card : ℝ) ≤ (300000 * Real.exp 4 * (3 : ℝ) ^ 17) *
      (P.totalDegree : ℝ) ^ 2 * (logarithmicBudget N : ℝ) ^ 17 := by
  have hk : 1 ≤ logarithmicBudget (2 * N) := by unfold logarithmicBudget; omega
  have hb := QuadraticRealIntegerGridCount.high_degree_count P hP (logarithmicBudget (2 * N)) hk hdegree
    N hN (log_le_budget (2 * N) (by omega)) S hcurve hbox
  have hm := mul_le_mul_of_nonneg_left (logarithmic_factors N hN)
    (show 0 ≤ 300000 * Real.exp 4 * (P.totalDegree : ℝ) ^ 2 by positivity)
  apply hb.trans
  convert hm using 1 <;> ring

end PaperP1.LogarithmicQuadraticPlaneParameters
