module

public import PaperP1.Algebra.CharlierQuadratic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Cast.Order.Ring

/-! # Exact integer endpoints of the negative second Charlier interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CharlierRoots

open PaperP1.CharlierQuadratic

def lowerRoot (μ : ℝ) : ℝ := μ + 1 / 2 - Real.sqrt (4 * μ + 1) / 2

def upperRoot (μ : ℝ) : ℝ := μ + 1 / 2 + Real.sqrt (4 * μ + 1) / 2

def lowerIndex (μ : ℝ) : ℕ := ⌊lowerRoot μ⌋₊ + 1

def upperIndex (μ : ℝ) : ℕ := ⌈upperRoot μ⌉₊ - 1

theorem root_bounds (μ : ℝ) (hμ : 0 < μ) :
    0 < lowerRoot μ ∧ lowerRoot μ + 1 < upperRoot μ := by
  have hnonneg : 0 ≤ 4 * μ + 1 := by linarith
  have hsquare := Real.sq_sqrt hnonneg
  have hspos := Real.sqrt_nonneg (4 * μ + 1)
  have hgap : 1 < Real.sqrt (4 * μ + 1) := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) < 4 * μ + 1)
    simpa only [Real.sqrt_one] using h
  have hupp : Real.sqrt (4 * μ + 1) < 2 * μ + 1 := by nlinarith [sq_pos_of_pos hμ]
  unfold lowerRoot upperRoot
  constructor <;> linarith

theorem quadratic_factor (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    quadratic μ k = ((k : ℝ) - lowerRoot μ) * ((k : ℝ) - upperRoot μ) := by
  have hsquare := Real.sq_sqrt (by linarith : 0 ≤ 4 * μ + 1)
  unfold quadratic lowerRoot upperRoot
  nlinarith

theorem quadratic_neg_iff_between (μ : ℝ) (hμ : 0 < μ) (k : ℕ) :
    quadratic μ k < 0 ↔ lowerRoot μ < (k : ℝ) ∧ (k : ℝ) < upperRoot μ := by
  have hroots := root_bounds μ hμ
  rw [quadratic_factor μ hμ.le]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨hlo, hup⟩ | ⟨hlo, hup⟩
    · constructor <;> linarith
    · exfalso
      linarith
  · rintro ⟨hlo, hup⟩
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

theorem indices_bounds (μ : ℝ) (hμ : 0 < μ) : 1 ≤ lowerIndex μ ∧ lowerIndex μ ≤ upperIndex μ := by
  have hroots := root_bounds μ hμ
  have hlo : (lowerIndex μ : ℝ) < upperRoot μ := by
    unfold lowerIndex
    push_cast
    linarith [Nat.floor_le hroots.1.le]
  have hceil : lowerIndex μ < ⌈upperRoot μ⌉₊ := Nat.lt_ceil.mpr hlo
  constructor
  · unfold lowerIndex
    omega
  · unfold upperIndex
    omega

theorem quadratic_neg_iff_indices (μ : ℝ) (hμ : 0 < μ) (k : ℕ) :
    quadratic μ k < 0 ↔ k ∈ Finset.Icc (lowerIndex μ) (upperIndex μ) := by
  have hroots := root_bounds μ hμ
  have hupper0 : (0 : ℝ) < upperRoot μ := by linarith
  have hceil : 0 < ⌈upperRoot μ⌉₊ := Nat.lt_ceil.mpr (by simpa only [Nat.cast_zero] using hupper0)
  rw [quadratic_neg_iff_between μ hμ, ← Nat.floor_lt hroots.1.le, ← Nat.lt_ceil]
  simp only [Finset.mem_Icc, lowerIndex, upperIndex]
  omega

end PaperP1.CharlierRoots
