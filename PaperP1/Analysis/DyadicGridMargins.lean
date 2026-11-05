module

public import PaperP1.Analysis.NormalizedGridSpacing
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

/-! # Actual dyadic endpoint bands for trimmed normalized grid parameters -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicGridMargins

open Set


def radius (N j : ℕ) : ℝ := (2 : ℝ) ^ j / (N : ℝ)

def sideDistance (i : Fin 2) (a b t : ℝ) : ℝ := if i = 0 then t - a else b - t

theorem radius_pos (N : ℕ) (hN : 0 < N) (j : ℕ) : 0 < radius N j := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_pos (by positivity) hNR

theorem exists_scale (N : ℕ) (hN : 0 < N) (d : ℝ) (hgap : 1 / (N : ℝ) ≤ d) (hbound : d ≤ 2) :
    ∃ j ≤ Nat.log2 (2 * N), radius N j ≤ d ∧ d < 2 * radius N j := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (1 : ℝ) ≤ (N : ℝ) * d := by
    have hh := (div_le_iff₀ hNR).mp hgap
    nlinarith only [hh]
  let m := ⌊(N : ℝ) * d⌋₊
  have hm : 1 ≤ m := Nat.le_floor (by simpa only [Nat.cast_one] using hx)
  have hupper : m ≤ 2 * N := Nat.floor_le_of_le (by push_cast; nlinarith only [hbound, hNR])
  have hlo : (2 : ℝ) ^ Nat.log2 m ≤ (N : ℝ) * d := by
    have hp : (2 : ℝ) ^ Nat.log2 m ≤ (m : ℝ) := by
      exact_mod_cast (by simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (show m ≠ 0 by omega))
    exact hp.trans (Nat.floor_le (zero_le_one.trans hx))
  have hhi : (N : ℝ) * d < 2 * (2 : ℝ) ^ Nat.log2 m := by
    have hp : m + 1 ≤ 2 ^ (Nat.log2 m + 1) := by
      have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
      simpa only [← Nat.log2_eq_log_two] using Nat.succ_le_of_lt hh
    have hpR : (m : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log2 m + 1) := by exact_mod_cast hp
    have hfloor : (N : ℝ) * d < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [pow_succ] at hpR
    nlinarith only [hfloor, hpR]
  refine ⟨Nat.log2 m, ?_, ?_, ?_⟩
  · simpa only [Nat.log2_eq_log_two] using (Nat.log_mono_right (b := 2) hupper)
  · apply (div_le_iff₀ hNR).mpr
    nlinarith only [hlo]
  · change d < 2 * ((2 : ℝ) ^ Nat.log2 m / (N : ℝ))
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hNR).mpr
    nlinarith only [hhi]

theorem sideDistance_abs_sub (i : Fin 2) (a b t u : ℝ) :
    |sideDistance i a b t - sideDistance i a b u| = |t - u| := by
  by_cases hi : i = 0
  · have ht : sideDistance i a b t = t - a := ite_eq_left hi
    have hu : sideDistance i a b u = u - a := ite_eq_left hi
    rw [ht, hu]
    congr 1
    ring
  · have ht : sideDistance i a b t = b - t := ite_eq_right hi
    have hu : sideDistance i a b u = b - u := ite_eq_right hi
    rw [ht, hu]
    have he : (b - t) - (b - u) = -(t - u) := by ring
    rw [he, abs_neg]

theorem exists_side_band (N : ℕ) (hN : 0 < N) (a b t : ℝ) (hwidth : b - a ≤ 2)
    (hleft : a + 1 / (N : ℝ) ≤ t) (hright : t ≤ b - 1 / (N : ℝ)) :
    ∃ i : Fin 2, ∃ j ≤ Nat.log2 (2 * N),
      0 < radius N j ∧ radius N j ≤ 1 ∧
      a + radius N j ≤ t ∧ t ≤ b - radius N j ∧
      sideDistance i a b t ∈ Ico (radius N j) (2 * radius N j) := by
  have hstep : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  by_cases hmid : t - a ≤ b - t
  · obtain ⟨j, hj, hlo, hhi⟩ := exists_scale N hN (t - a) (by linarith only [hleft])
      (by linarith only [hwidth, hright, hstep])
    refine ⟨0, j, hj, radius_pos N hN j, ?_, ?_, ?_, ?_⟩
    · linarith only [hlo, hmid, hwidth]
    · linarith only [hlo]
    · linarith only [hlo, hmid]
    · exact ⟨hlo, hhi⟩
  · obtain ⟨j, hj, hlo, hhi⟩ := exists_scale N hN (b - t) (by linarith only [hright])
      (by linarith only [hwidth, hleft, hstep])
    refine ⟨1, j, hj, radius_pos N hN j, ?_, ?_, ?_, ?_⟩
    · linarith only [hlo, hmid, hwidth]
    · linarith only [hlo, hmid]
    · linarith only [hlo]
    · change radius N j ≤ b - t ∧ b - t < 2 * radius N j
      exact ⟨hlo, hhi⟩

end PaperP1.DyadicGridMargins
