module

public import PaperP1.Arithmetic.QuadraticDegreeUniformFieldCount
public import Mathlib.Data.Fintype.BigOperators

/-! # Actual integer box populations absorb the large-degree and unit-height regimes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPopulationBoxBudget

open QuadraticDegreeUniformFieldCount CurveIntegerFibres

theorem box_card (n H : ℕ) (S : Finset (Fin n → ℤ))
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) : S.card ≤ (2 * H + 1) ^ n := by
  classical
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin n ↦ offsetBox H) := by
    intro w hw
    apply Fintype.mem_piFinset.mpr
    intro i
    rw [mem_offsetBox, Int.abs_eq_natAbs]
    exact_mod_cast hheight w hw i
  have hh := Finset.card_le_card hsub
  rwa [Fintype.card_piFinset_const, LinearPlaneGridBound.offsetBox_card] at hh

theorem dimension_power (n H : ℕ) (hH : 1 ≤ H) (S : Finset (Fin n → ℤ))
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) : S.card ≤ 3 ^ n * H ^ n := by
  calc
    _ ≤ (2 * H + 1) ^ n := box_card n H S hheight
    _ ≤ (3 * H) ^ n := Nat.pow_le_pow_left (by omega) n
    _ = _ := mul_pow 3 H n

theorem large_degree (n d H : ℕ) (hd : 0 < d) (hH : 1 ≤ H) (hcap : H ^ n < d)
    (S : Finset (Fin n → ℤ)) (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    S.card ≤ 3 ^ n * d ^ 2 := by
  have hd2 : d ≤ d ^ 2 := le_self_pow₀ (by omega) (by decide : 2 ≠ 0)
  exact (dimension_power n H hH S hheight).trans (Nat.mul_le_mul_left _ (hcap.le.trans hd2))

theorem large_degree_profile (n d H : ℕ) (hd : 0 < d) (hH : 1 ≤ H) (hcap : H ^ n < d)
    (S : Finset (Fin n → ℤ)) (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    (S.card : ℝ) ≤ ((3 ^ n : ℕ) : ℝ) * profile d H := by
  have hc : (S.card : ℝ) ≤ ((3 ^ n : ℕ) : ℝ) * (d : ℝ) ^ 2 := by
    exact_mod_cast large_degree n d H hd hH hcap S hheight
  exact hc.trans (mul_le_mul_of_nonneg_left (degree_square_le_profile d H hH) (Nat.cast_nonneg _))

theorem unit_height_profile (n d : ℕ) (hd : 0 < d) (S : Finset (Fin n → ℤ))
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ 1) :
    (S.card : ℝ) ≤ ((3 ^ n : ℕ) : ℝ) * profile d 1 := by
  have hc : (S.card : ℝ) ≤ ((3 ^ n : ℕ) : ℝ) := by
    exact_mod_cast (show S.card ≤ 3 ^ n by simpa only [mul_one, one_pow] using dimension_power n 1 (by decide) S hheight)
  have hD : (1 : ℝ) ≤ (d : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ d by omega))
  exact hc.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (hD.trans (degree_square_le_profile d 1 (by decide))))

end PaperP1.IntegerPopulationBoxBudget
