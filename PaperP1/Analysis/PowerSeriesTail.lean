module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # A positive p-series tail at an arbitrary real threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PowerSeriesTail

open Finset Set MeasureTheory

def weight (s : ℝ) (n : ℕ) : ℝ := (n + 1 : ℝ) ^ (-s)

def tailTerm (s T : ℝ) (n : ℕ) : ℝ := if T < (n + 1 : ℝ) then weight s n else 0

def tail (s T : ℝ) : ℝ := ∑' n, tailTerm s T n

def total (s : ℝ) : ℝ := ∑' n, weight s n

def constant (s : ℝ) : ℝ := (2 : ℝ) ^ (s - 1) / (s - 1)

theorem weight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ weight s n := by
  unfold weight
  positivity

theorem tailTerm_nonneg (s T : ℝ) (n : ℕ) : 0 ≤ tailTerm s T n := by
  unfold tailTerm
  split_ifs
  · exact weight_nonneg s n
  · exact le_rfl

theorem tailTerm_le_weight (s T : ℝ) (n : ℕ) : tailTerm s T n ≤ weight s n := by
  unfold tailTerm
  split_ifs
  · exact le_rfl
  · exact weight_nonneg s n

theorem summable_weight (s : ℝ) (hs : 1 < s) : Summable (weight s) := by
  have h : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  convert (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-s)) 1).mpr h using 1
  funext n
  simp only [weight, Nat.cast_add, Nat.cast_one]

theorem summable_tailTerm (s T : ℝ) (hs : 1 < s) : Summable (tailTerm s T) :=
  (summable_weight s hs).of_nonneg_of_le (tailTerm_nonneg s T) (tailTerm_le_weight s T)

theorem total_nonneg (s : ℝ) : 0 ≤ total s := tsum_nonneg (weight_nonneg s)

theorem tail_nonneg (s T : ℝ) : 0 ≤ tail s T := tsum_nonneg (tailTerm_nonneg s T)

theorem tail_le_total (s T : ℝ) (hs : 1 < s) : tail s T ≤ total s :=
  (summable_tailTerm s T hs).tsum_le_tsum (tailTerm_le_weight s T) (summable_weight s hs)

theorem tail_eq_shifted (s T : ℝ) (hs : 1 < s) (hT : 0 ≤ T) :
    tail s T = ∑' n : ℕ, (n + Nat.floor T + 1 : ℝ) ^ (-s) := by
  have hzero : (∑ n ∈ range (Nat.floor T), tailTerm s T n) = 0 := by
    apply sum_eq_zero
    intro n hn
    have hnT : (n + 1 : ℝ) ≤ T := by
      have hnat : n + 1 ≤ Nat.floor T := mem_range.mp hn
      exact (by exact_mod_cast hnat : (n + 1 : ℝ) ≤ Nat.floor T).trans (Nat.floor_le hT)
    exact ite_eq_right (not_lt_of_ge hnT)
  unfold tail
  rw [← (summable_tailTerm s T hs).sum_add_tsum_nat_add (Nat.floor T), hzero, zero_add]
  apply tsum_congr
  intro n
  have hnT : T < (n + Nat.floor T + 1 : ℝ) := by
    have h := Nat.lt_floor_add_one T
    have hn := Nat.cast_nonneg n (α := ℝ)
    linarith
  simp only [tailTerm, weight, Nat.cast_add]
  rw [ite_eq_left hnT]

theorem floor_ge_half (T : ℝ) (hT : 1 ≤ T) : T / 2 ≤ (Nat.floor T : ℝ) := by
  have hfloor : 1 ≤ Nat.floor T := (Nat.one_le_floor_iff T).mpr hT
  have hcast : (1 : ℝ) ≤ Nat.floor T := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one T
  linarith

theorem constant_pos (s : ℝ) (hs : 1 < s) : 0 < constant s := by
  unfold constant
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)

theorem tail_le_power (s : ℝ) (hs : 1 < s) (T : ℝ) (hT : 1 ≤ T) :
    tail s T ≤ constant s * T ^ (1 - s) := by
  have hfloor : 1 ≤ Nat.floor T := (Nat.one_le_floor_iff T).mpr hT
  have hfpos : (0 : ℝ) < Nat.floor T := by exact_mod_cast (by omega : 0 < Nat.floor T)
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-s)) (Ici (Nat.floor T : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hfpos.trans_le hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hfpos
  have h := hanti.tsum_comp_add_le_integral (Nat.floor T) hint
    (fun x hx ↦ Real.rpow_nonneg (hfpos.le.trans hx.le) _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hfpos] at h
  have hpow : (Nat.floor T : ℝ) ^ (1 - s) ≤ (T / 2) ^ (1 - s) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (floor_ge_half T hT) (by linarith)
  have hden : 0 < s - 1 := by linarith
  calc
    _ = ∑' n : ℕ, (n + Nat.floor T + 1 : ℝ) ^ (-s) := tail_eq_shifted s T hs (by linarith)
    _ ≤ (Nat.floor T : ℝ) ^ (1 - s) / (s - 1) := by
      convert h using 1
      · simp only [Nat.cast_add, Nat.cast_one]
      · rw [show -s + 1 = 1 - s by ring]
        rw [show (1 - s) = -(s - 1) by ring, neg_div_neg_eq]
    _ ≤ (T / 2) ^ (1 - s) / (s - 1) := div_le_div_of_nonneg_right hpow hden.le
    _ = _ := by
      rw [Real.div_rpow (by linarith : 0 ≤ T) (by norm_num : (0 : ℝ) ≤ 2)]
      unfold constant
      rw [show 1 - s = -(s - 1) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp

end PaperP1.PowerSeriesTail
