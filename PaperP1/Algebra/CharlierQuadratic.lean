module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! # Exact integer minimum of the second Charlier quadratic

The nonnegative domain is the natural numbers. Choosing floor(μ)+1 also
works when μ is an integer, when there are two minimizing integers.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CharlierQuadratic

def theta (μ : ℝ) : ℝ := μ - (⌊μ⌋₊ : ℝ)

def quadratic (μ : ℝ) (k : ℕ) : ℝ := ((k : ℝ) - μ) ^ 2 - k

def minimumMagnitude (μ : ℝ) : ℝ := μ + theta μ * (1 - theta μ)

theorem theta_eq_fract (μ : ℝ) (hμ : 0 ≤ μ) : theta μ = Int.fract μ := by
  unfold theta Int.fract
  rw [← Int.natCast_floor_eq_floor hμ, Int.cast_natCast]

theorem theta_nonneg (μ : ℝ) (hμ : 0 ≤ μ) : 0 ≤ theta μ :=
  sub_nonneg.mpr (Nat.floor_le hμ)

theorem theta_lt_one (μ : ℝ) : theta μ < 1 := by
  have h := Nat.lt_floor_add_one μ
  unfold theta
  linarith

theorem minimumMagnitude_pos (μ : ℝ) (hμ : 0 < μ) : 0 < minimumMagnitude μ := by
  have hprod : 0 ≤ theta μ * (1 - theta μ) :=
    mul_nonneg (theta_nonneg μ hμ.le) (sub_nonneg.mpr (theta_lt_one μ).le)
  exact add_pos_of_pos_of_nonneg hμ hprod

theorem quadratic_at_floor_succ (μ : ℝ) :
    quadratic μ (⌊μ⌋₊ + 1) = -minimumMagnitude μ := by
  unfold quadratic minimumMagnitude theta
  push_cast
  ring

theorem quadratic_minus_minimum (μ : ℝ) (k : ℕ) :
    quadratic μ k + minimumMagnitude μ =
      ((k : ℝ) - (⌊μ⌋₊ : ℝ) - 1) * ((k : ℝ) - (⌊μ⌋₊ : ℝ) - 2 * theta μ) := by
  unfold quadratic minimumMagnitude theta
  ring

theorem quadratic_ge_minimum (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    -minimumMagnitude μ ≤ quadratic μ k := by
  have hθ := theta_nonneg μ hμ
  have hθone := theta_lt_one μ
  have hid := quadratic_minus_minimum μ k
  by_cases hk : k ≤ ⌊μ⌋₊
  · have hkR : (k : ℝ) ≤ (⌊μ⌋₊ : ℝ) := by exact_mod_cast hk
    have hp : 0 ≤ ((⌊μ⌋₊ : ℝ) + 1 - k) * ((⌊μ⌋₊ : ℝ) + 2 * theta μ - k) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · by_cases heq : k = ⌊μ⌋₊ + 1
    · rw [heq, quadratic_at_floor_succ]
    · have hkR : (⌊μ⌋₊ : ℝ) + 2 ≤ (k : ℝ) := by
        exact_mod_cast (show ⌊μ⌋₊ + 2 ≤ k by omega)
      have hp : 0 ≤ ((k : ℝ) - (⌊μ⌋₊ : ℝ) - 1) *
          ((k : ℝ) - (⌊μ⌋₊ : ℝ) - 2 * theta μ) :=
        mul_nonneg (by linarith) (by linarith)
      linarith

theorem quadratic_ge_count (μ : ℝ) (k : ℕ) (hk : 2 * μ + 4 ≤ (k : ℝ)) :
    (k : ℝ) ≤ quadratic μ k := by
  have hkzero : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ (k : ℝ) / 2 + 2 := by linarith
  have hsq := mul_self_le_mul_self hs (show (k : ℝ) / 2 + 2 ≤ (k : ℝ) - μ by linarith)
  unfold quadratic
  nlinarith [sq_nonneg ((k : ℝ) / 2)]

theorem nonnegative_scaled_iff (μ α : ℝ) (hμ : 0 < μ) :
    (∀ k : ℕ, 0 ≤ 2 * μ ^ 2 + α * quadratic μ k) ↔
      0 ≤ α ∧ α ≤ 2 * μ ^ 2 / minimumMagnitude μ := by
  have hmin := minimumMagnitude_pos μ hμ
  constructor
  · intro h
    have hα : 0 ≤ α := by
      by_contra hn
      have hαneg : α < 0 := lt_of_not_ge hn
      obtain ⟨k, hk⟩ := exists_nat_gt (max (2 * μ + 4) (-2 * μ ^ 2 / α))
      have hkbase : 2 * μ + 4 ≤ (k : ℝ) := (le_max_left _ _).trans hk.le
      have hktail : -2 * μ ^ 2 / α < (k : ℝ) := (le_max_right _ _).trans_lt hk
      have hquad := quadratic_ge_count μ k hkbase
      have htail : -2 * μ ^ 2 / α < quadratic μ k := hktail.trans_le hquad
      have hprod : α * quadratic μ k < -2 * μ ^ 2 := by
        have hm := mul_lt_mul_of_neg_left htail hαneg
        have heq : α * (-2 * μ ^ 2 / α) = -2 * μ ^ 2 := by
          field_simp [hαneg.ne]
        rwa [heq] at hm
      linarith [h k]
    refine ⟨hα, (le_div_iff₀ hmin).mpr ?_⟩
    have hfloor := h (⌊μ⌋₊ + 1)
    rw [quadratic_at_floor_succ] at hfloor
    nlinarith
  · rintro ⟨hα, hbound⟩ k
    have hprod := mul_le_mul_of_nonneg_left (quadratic_ge_minimum μ hμ.le k) hα
    have hupper := (le_div_iff₀ hmin).mp hbound
    nlinarith

theorem bracket_nonnegative_iff (μ α : ℝ) (hμ : 0 < μ) :
    (∀ k : ℕ, 0 ≤ 1 + α / (2 * μ ^ 2) * quadratic μ k) ↔
      0 ≤ α ∧ α ≤ 2 * μ ^ 2 / (μ + theta μ * (1 - theta μ)) := by
  have hden : 0 < 2 * μ ^ 2 := by positivity
  have hid (k : ℕ) : 1 + α / (2 * μ ^ 2) * quadratic μ k =
      (2 * μ ^ 2 + α * quadratic μ k) / (2 * μ ^ 2) := by
    field_simp
  simp_rw [hid, le_div_iff₀ hden, zero_mul]
  exact nonnegative_scaled_iff μ α hμ

end PaperP1.CharlierQuadratic
