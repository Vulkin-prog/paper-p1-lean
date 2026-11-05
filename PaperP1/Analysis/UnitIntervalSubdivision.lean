module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! # Explicit interior centers for a finite subdivision of the open unit interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitIntervalSubdivision

open Set


def index (M : ℕ) (t : ℝ) : ℕ := ⌊(M : ℝ) * t⌋₊

def center (M : ℕ) (i : Fin M) : ℝ := ((i.val : ℝ) + 1 / 2) / (M : ℝ)

theorem index_lt (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    index M t < M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Nat.floor_lt (mul_nonneg hMR.le ht.1.le)).mpr
  nlinarith only [ht.2, hMR]

theorem center_mem (M : ℕ) (hM : 0 < M) (i : Fin M) : center M i ∈ Ioo (0 : ℝ) 1 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hi : (i.val : ℝ) + 1 ≤ M := by exact_mod_cast i.isLt
  exact ⟨div_pos (by positivity) hMR, (div_lt_one hMR).mpr (by linarith only [hi])⟩

theorem distance_bound (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (i : Fin M) (hi : index M t = i.val) : |t - center M i| ≤ 1 / (M : ℝ) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hnon : (0 : ℝ) ≤ (M : ℝ) * t := mul_nonneg hMR.le ht.1.le
  have hlo := Nat.floor_le hnon
  have hhi := Nat.lt_floor_add_one ((M : ℝ) * t)
  change ((index M t : ℕ) : ℝ) ≤ (M : ℝ) * t at hlo
  change (M : ℝ) * t < ((index M t : ℕ) : ℝ) + 1 at hhi
  rw [hi] at hlo hhi
  have hd : |(M : ℝ) * t - ((i.val : ℝ) + 1 / 2)| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
  have he : t - center M i = ((M : ℝ) * t - ((i.val : ℝ) + 1 / 2)) / (M : ℝ) := by
    dsimp only [center]
    field_simp
  rw [he, abs_div, abs_of_pos hMR]
  exact div_le_div_of_nonneg_right hd hMR.le

end PaperP1.UnitIntervalSubdivision
