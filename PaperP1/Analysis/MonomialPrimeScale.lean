module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Exact monomial scales imply both strict prime-power comparisons -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonomialPrimeScale

theorem strict_power_domination (C D L V α β P : ℝ) (A B N : ℕ)
    (hC : 1 ≤ C) (hD : D < C) (hL : 1 ≤ L) (hV : 1 ≤ V) (hN : 1 ≤ N)
    (hA : (A : ℝ) ≤ α * N) (hB : (B : ℝ) ≤ β * N)
    (hP : C * L ^ α * V ^ β ≤ P) : D * L ^ A * V ^ B < P ^ N := by
  have hL0 : 0 < L := by linarith
  have hV0 : 0 < V := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCN : C ≤ C ^ N := le_self_pow₀ hC (by omega)
  have hLA : L ^ A ≤ L ^ (α * N) := by
    rw [← Real.rpow_natCast L A]
    exact Real.rpow_le_rpow_of_exponent_le hL hA
  have hVB : V ^ B ≤ V ^ (β * N) := by
    rw [← Real.rpow_natCast V B]
    exact Real.rpow_le_rpow_of_exponent_le hV hB
  calc
    D * L ^ A * V ^ B < C * L ^ A * V ^ B := by gcongr
    _ ≤ C ^ N * L ^ (α * N) * V ^ (β * N) := by gcongr
    _ = (C * L ^ α * V ^ β) ^ N := by
      rw [Real.rpow_mul_natCast (by linarith : 0 ≤ L),
        Real.rpow_mul_natCast (by linarith : 0 ≤ V), mul_pow, mul_pow]
    _ ≤ P ^ N := pow_le_pow_left₀ (by positivity) hP _

theorem rounded_base (C L V α β : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L) (hV : 1 ≤ V)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ P : ℕ, 0 < P ∧ C * L ^ α * V ^ β ≤ (P : ℝ) ∧
      (P : ℝ) ≤ 2 * (C * L ^ α * V ^ β) := by
  let W := C * L ^ α * V ^ β
  have hLA : 1 ≤ L ^ α := Real.one_le_rpow hL hα
  have hVB : 1 ≤ V ^ β := Real.one_le_rpow hV hβ
  have hW : 1 ≤ W := by
    exact (by norm_num : (1 : ℝ) = 1 * 1 * 1).trans_le
      (mul_le_mul (mul_le_mul hC hLA (by norm_num) (by positivity)) hVB (by norm_num) (by positivity))
  refine ⟨⌈W⌉₊, Nat.ceil_pos.mpr (by linarith), Nat.le_ceil W, ?_⟩
  exact (Nat.ceil_lt_add_one (by linarith : 0 ≤ W)).le.trans (by linarith)

theorem determinant_monomial (a H J k : ℕ) (L V : ℝ) :
    (k.factorial : ℝ) * (L ^ H * (((a : ℝ) + 1) * V * L ^ a) ^ J) ^ k =
      ((k.factorial : ℝ) * ((a : ℝ) + 1) ^ (J * k)) * L ^ (H * k + a * J * k) * V ^ (J * k) := by
  simp only [mul_pow, pow_mul, pow_add]
  ring

theorem obstruction_monomial (a b : ℕ) (L V : ℝ) :
    ((a : ℝ) + 1) * ((b : ℝ) + 1) * b * V * L ^ (a + 1) *
        (((a : ℝ) + 1) * V * L ^ a) ^ b =
      (((a : ℝ) + 1) * ((b : ℝ) + 1) * b * ((a : ℝ) + 1) ^ b) *
        L ^ (a * b + a + 1) * V ^ (b + 1) := by
  simp only [mul_pow, pow_mul, pow_add, pow_one]
  ring

theorem determinant_small (a H J k N : ℕ) (C L V α β P : ℝ)
    (hC : 1 ≤ C) (hD : (k.factorial : ℝ) * ((a : ℝ) + 1) ^ (J * k) < C)
    (hL : 1 ≤ L) (hV : 1 ≤ V) (hN : 1 ≤ N)
    (hA : ((H * k + a * J * k : ℕ) : ℝ) ≤ α * N)
    (hB : ((J * k : ℕ) : ℝ) ≤ β * N) (hP : C * L ^ α * V ^ β ≤ P) :
    (k.factorial : ℝ) * (L ^ H * (((a : ℝ) + 1) * V * L ^ a) ^ J) ^ k < P ^ N := by
  rw [determinant_monomial]
  exact strict_power_domination C _ L V α β P _ _ N hC hD hL hV hN hA hB hP

theorem obstruction_small (a b m : ℕ) (C L V α β P : ℝ)
    (hC : 1 ≤ C)
    (hD : ((a : ℝ) + 1) * ((b : ℝ) + 1) * b * ((a : ℝ) + 1) ^ b < C)
    (hL : 1 ≤ L) (hV : 1 ≤ V) (hm : 1 ≤ m)
    (hA : ((a * b + a + 1 : ℕ) : ℝ) ≤ α * m)
    (hB : ((b + 1 : ℕ) : ℝ) ≤ β * m) (hP : C * L ^ α * V ^ β ≤ P) :
    ((a : ℝ) + 1) * ((b : ℝ) + 1) * b * V * L ^ (a + 1) *
      (((a : ℝ) + 1) * V * L ^ a) ^ b < P ^ m := by
  rw [obstruction_monomial]
  exact strict_power_domination C _ L V α β P _ _ m hC hD hL hV hm hA hB hP

end PaperP1.MonomialPrimeScale
