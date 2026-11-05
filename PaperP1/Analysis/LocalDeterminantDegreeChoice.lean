module

public import PaperP1.Analysis.MonomialPrimeScale
public import Mathlib.Algebra.Group.Nat.Even

/-! # Uniform auxiliary degree and avoidance power at the sharp biform exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalDeterminantDegreeChoice

theorem triangle_weight (k : ℕ) (hk : 2 ≤ k) :
    1 ≤ k * (k - 1) / 2 ∧
      2 * ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
  have he : 2 * (k * (k - 1) / 2) = k * (k - 1) :=
    Nat.mul_div_cancel' k.even_mul_pred_self.two_dvd
  constructor
  · have hpred : 1 ≤ k - 1 := by omega
    have hprod : 2 ≤ k * (k - 1) := by nlinarith
    omega
  · have hc : (2 : ℝ) * ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast he
    have hp : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hp] at hc
    exact hc

theorem exists_auxiliary_degree (a b : ℕ) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, 1 ≤ H ∧
      let J := b - 1
      let k := (H + 1) * (J + 1)
      let N := k * (k - 1) / 2
      1 ≤ N ∧ (((H * k + a * J * k : ℕ) : ℝ) ≤ (2 / (b : ℝ) + ε / 2) * N) ∧
        (((J * k : ℕ) : ℝ) ≤ (ε / 2) * N) := by
  obtain ⟨H, hHgt⟩ := exists_nat_gt (max 1 (8 * ((a : ℝ) + 1) * ((b : ℝ) + 1) / ε))
  have hH : 1 ≤ H := by exact_mod_cast ((le_max_left _ _).trans_lt hHgt).le
  refine ⟨H, hH, ?_⟩
  let J := b - 1
  let k := (H + 1) * (J + 1)
  let N := k * (k - 1) / 2
  change 1 ≤ N ∧ (((H * k + a * J * k : ℕ) : ℝ) ≤ (2 / (b : ℝ) + ε / 2) * N) ∧
    (((J * k : ℕ) : ℝ) ≤ (ε / 2) * N)
  have hJ : J + 1 = b := by dsimp [J]; omega
  have hk : k = (H + 1) * b := by dsimp only [k]; rw [hJ]
  have hkfour : 4 ≤ k := by rw [hk]; nlinarith
  obtain ⟨hN, htwoN⟩ := triangle_weight k (by omega)
  have haR : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hkR : (k : ℝ) = ((H : ℝ) + 1) * b := by rw [hk]; push_cast; rfl
  have hJR : (J : ℝ) = (b : ℝ) - 1 := by dsimp [J]; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbig : 8 * ((a : ℝ) + 1) * ((b : ℝ) + 1) < ε * H := by
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hHgt)
    nlinarith
  have hkH : (H : ℝ) ≤ (k : ℝ) - 1 := by
    rw [hkR]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ H + 1) (by linarith : (0 : ℝ) ≤ b - 2)]
  have hεK := mul_le_mul_of_nonneg_left hkH hε.le
  have hdiv : 2 * (H : ℝ) ≤ (2 / (b : ℝ)) * ((k : ℝ) - 1) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hb0).mpr
    rw [hkR]
    nlinarith
  have hab : (0 : ℝ) ≤ (a : ℝ) * b := mul_nonneg haR (by linarith)
  have hx : 2 * ((H : ℝ) + (a : ℝ) * J) ≤ (2 / (b : ℝ) + ε / 2) * ((k : ℝ) - 1) := by
    rw [hJR]
    nlinarith
  have hy : 2 * (J : ℝ) ≤ (ε / 2) * ((k : ℝ) - 1) := by
    rw [hJR]
    nlinarith
  refine ⟨hN, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg (α := ℝ) k)
    have hh : 2 * (((H * k + a * J * k : ℕ) : ℝ)) ≤
        (2 / (b : ℝ) + ε / 2) * (2 * (N : ℝ)) := by
      rw [htwoN]
      push_cast
      nlinarith
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right hy (Nat.cast_nonneg (α := ℝ) k)
    have hh : 2 * (((J * k : ℕ) : ℝ)) ≤ (ε / 2) * (2 * (N : ℝ)) := by
      rw [htwoN]
      push_cast
      nlinarith
    nlinarith

theorem exists_avoidance_power (A B : ℕ) (α β : ℝ) (hβ : 0 < β) (hα : β ≤ α) :
    ∃ m : ℕ, 1 ≤ m ∧ (A : ℝ) ≤ α * m ∧ (B : ℝ) ≤ β * m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (((A : ℝ) + B + 1) / β))
  have hmNat : 1 ≤ m := by exact_mod_cast ((le_max_left _ _).trans_lt hm).le
  have hh := (div_lt_iff₀ hβ).mp ((le_max_right _ _).trans_lt hm)
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hscale := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg (α := ℝ) m)
  refine ⟨m, hmNat, ?_, ?_⟩ <;> nlinarith

end PaperP1.LocalDeterminantDegreeChoice
