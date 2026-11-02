module

public import PaperP1.Analysis.ElementaryLogGrowth
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Explicit branching and radius parameters for the actual finite short-basis construction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisParameters

def branching (B : ℝ) : ℕ := ⌊Real.sqrt (Real.log B)⌋₊

def radius (B : ℝ) (n : ℕ) : ℕ := Nat.log (branching B) n + 1

theorem branching_bounds (B : ℝ) (hs : 64 ≤ Real.log B) :
    2 ≤ branching B ∧ (branching B : ℝ) ≤ Real.sqrt (Real.log B) ∧
      Real.sqrt (Real.log B) / 2 ≤ (branching B : ℝ) := by
  have hs₀ : 0 ≤ Real.log B := by linarith
  have hr₀ := Real.sqrt_nonneg (Real.log B)
  have hsq := Real.sq_sqrt hs₀
  have hr : (4 : ℝ) ≤ Real.sqrt (Real.log B) := by nlinarith
  have hd : 2 ≤ branching B := by
    apply Nat.le_floor
    norm_num
    linarith
  have hfloor := Nat.floor_le hr₀
  have hlt := Nat.lt_floor_add_one (Real.sqrt (Real.log B))
  exact ⟨hd, hfloor, by dsimp [branching]; linarith⟩

theorem branching_log_lower (B : ℝ) (hs : 64 ≤ Real.log B)
    (hl : 4 ≤ Real.log (Real.log B)) :
    Real.log (Real.log B) / 4 ≤ Real.log (branching B : ℝ) := by
  obtain ⟨_hd, _hdup, hdlow⟩ := branching_bounds B hs
  have hs₀ : 0 < Real.log B := by linarith
  have hr : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.mpr hs₀
  have hm := Real.log_le_log (div_pos hr (by norm_num)) hdlow
  rw [Real.log_div (ne_of_gt hr) (by norm_num), Real.log_sqrt hs₀.le] at hm
  have htwo : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  linarith

theorem radius_power (B : ℝ) (n : ℕ) (hs : 64 ≤ Real.log B) :
    n < branching B ^ radius B n :=
  Nat.lt_pow_succ_log_self (by have h := (branching_bounds B hs).1; omega) n

theorem radius_length_bound (B : ℝ) (n : ℕ) (hB : 1 < B)
    (hs : 64 ≤ Real.log B) (hl : 4 ≤ Real.log (Real.log B))
    (hn : 0 < n) (hnB : (n : ℝ) ≤ B) :
    ((2 * radius B n + 1 : ℕ) : ℝ) ≤ 11 * Real.log B / Real.log (Real.log B) := by
  have hs₀ : 0 < Real.log B := Real.log_pos hB
  have hl₀ : 0 < Real.log (Real.log B) := by linarith
  have hdlog := branching_log_lower B hs hl
  have hdpos : 0 < Real.log (branching B : ℝ) := by linarith
  have hnat := Real.natLog_le_logb n (branching B)
  change (Nat.log (branching B) n : ℝ) ≤ Real.log n / Real.log (branching B : ℝ) at hnat
  have hmul := (le_div_iff₀ hdpos).mp hnat
  have hnlog : Real.log (n : ℝ) ≤ Real.log B := Real.log_le_log (by exact_mod_cast hn) hnB
  have hprod := mul_le_mul_of_nonneg_left hdlog (Nat.cast_nonneg (Nat.log (branching B) n))
  have hll : Real.log (Real.log B) ≤ Real.log B := Real.log_le_self hs₀.le
  apply (le_div_iff₀ hl₀).mpr
  dsimp [radius]
  push_cast
  nlinarith

theorem vertex_count_le_scale (B : ℝ) (n : ℕ) (hB : 0 ≤ B) (hs : 64 ≤ Real.log B)
    (hn : (n : ℝ) ≤ 24 * B / Real.log B) : (n : ℝ) ≤ B := by
  have hs₀ : 0 < Real.log B := by linarith
  have hm := (le_div_iff₀ hs₀).mp hn
  have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem residual_bound (B : ℝ) (n : ℕ) (hs : 64 ≤ Real.log B)
    (hn : (n : ℝ) ≤ 24 * B / Real.log B) :
    (((2 * branching B) * n : ℕ) : ℝ) ≤ 48 * B / Real.sqrt (Real.log B) := by
  have hs₀ : 0 < Real.log B := by linarith
  have hr : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.mpr hs₀
  have hd := (branching_bounds B hs).2.1
  have hm := (le_div_iff₀ hs₀).mp hn
  have hsq := Real.sq_sqrt hs₀.le
  apply (le_div_iff₀ hr).mpr
  push_cast
  calc
    2 * (branching B : ℝ) * n * Real.sqrt (Real.log B) ≤
        2 * Real.sqrt (Real.log B) * n * Real.sqrt (Real.log B) := by
      gcongr
    _ = 2 * (n : ℝ) * Real.log B := by nlinarith [hsq]
    _ ≤ 48 * B := by linarith

theorem logarithmic_threshold (a : ℝ) (ha : 0 < a) :
    ∃ B₀ : ℕ, ∀ B ≥ B₀, 2 ≤ B ∧ 64 ≤ Real.log (B : ℝ) ∧
      4 ≤ Real.log (Real.log (B : ℝ)) ∧ 4 ≤ a * Real.log (B : ℝ) := by
  obtain ⟨B₀, hB₀⟩ := ElementaryLogGrowth.log_ge_eventually
    (max 64 (max (Real.exp 4) (4 / a)))
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨hlog, htwo⟩ := hB₀ B hB
  have hs : 64 ≤ Real.log (B : ℝ) := (le_max_left _ _).trans hlog
  have he : Real.exp 4 ≤ Real.log (B : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
  have haB : 4 / a ≤ Real.log (B : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlog)
  refine ⟨htwo, hs, ?_, ?_⟩
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 4) he
  · have hm := (div_le_iff₀ ha).mp haB
    linarith

end PaperP1.ShortBasisParameters
