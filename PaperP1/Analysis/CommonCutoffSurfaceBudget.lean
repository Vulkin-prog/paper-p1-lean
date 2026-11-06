module

public import PaperP1.Analysis.P3SurfaceDivisorLimits
public import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonCutoffSurfaceBudget

open Finset

def cutoff (k s : ℕ) : ℕ := ⌊Real.sqrt (2 * (s : ℝ) / (k : ℝ))⌋₊

theorem real_floor_budget (A K : ℝ) (hA : 0 ≤ A) (hK : 0 < K) :
    (2 / 3 : ℝ) * A * Real.sqrt (2 * A / K) - 3 * A ≤
      (⌊Real.sqrt (2 * A / K)⌋₊ : ℝ) * A - K *
        (⌊Real.sqrt (2 * A / K)⌋₊ : ℝ) * ((⌊Real.sqrt (2 * A / K)⌋₊ : ℝ) + 1) *
        ((⌊Real.sqrt (2 * A / K)⌋₊ : ℝ) + 2) / 6 := by
  let t := Real.sqrt (2 * A / K)
  let L : ℕ := ⌊t⌋₊
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hL : (L : ℝ) ≤ t := Nat.floor_le ht
  have hLt : t < (L : ℝ) + 1 := Nat.lt_floor_add_one t
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  change (2 / 3 : ℝ) * A * t - 3 * A ≤
    (L : ℝ) * A - K * (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 6
  by_cases ht1 : t < 1
  · have hLz : L = 0 := by
      have hh : (L : ℝ) < 1 := hL.trans_lt ht1
      have hn : L < 1 := by exact_mod_cast hh
      omega
    rw [hLz]
    norm_num
    nlinarith [mul_nonneg hA (show 0 ≤ 1 - t by linarith)]
  · have ht1' : 1 ≤ t := le_of_not_gt ht1
    have htsq : K * t ^ 2 = 2 * A := by
      dsimp only [t]
      rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hA) hK.le)]
      field_simp [hK.ne']
    have hfirst : (t - 1) * A ≤ (L : ℝ) * A :=
      mul_le_mul_of_nonneg_right (by linarith) hA
    have hsquare : K * (L : ℝ) ^ 2 ≤ 2 * A := by
      calc
        _ ≤ K * t ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 2) hK.le
        _ = _ := htsq
    have hcube : K * (L : ℝ) ^ 3 ≤ 2 * A * t := by
      calc
        _ ≤ K * t ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 3) hK.le
        _ = (K * t ^ 2) * t := by ring
        _ = _ := by rw [htsq]
    have hlinear : K * (L : ℝ) ≤ 2 * A := by
      have ht_sq : t ≤ t ^ 2 := by nlinarith
      calc
        _ ≤ K * t := mul_le_mul_of_nonneg_left hL hK.le
        _ ≤ K * t ^ 2 := mul_le_mul_of_nonneg_left ht_sq hK.le
        _ = _ := htsq
    nlinarith only [hfirst, hsquare, hcube, hlinear, hA]

theorem class_budget {χ : Type*} [Fintype χ] (n : χ → ℕ) :
    (2 / 3 : ℝ) * (∑ c, n c : ℕ) *
        Real.sqrt (2 * (∑ c, n c : ℕ) / (Fintype.card χ : ℝ)) - 3 * (∑ c, n c : ℕ) ≤
      ((∑ c, (cutoff (Fintype.card χ) (∑ c, n c) * n c -
        (cutoff (Fintype.card χ) (∑ c, n c) + 2).choose 3) : ℕ) : ℝ) := by
  classical
  by_cases hk : Fintype.card χ = 0
  · let : IsEmpty χ := Fintype.card_eq_zero_iff.mp hk
    simp
  · let L := cutoff (Fintype.card χ) (∑ c, n c)
    let B := (L + 2).choose 3
    have hlocal (c : χ) : (L : ℝ) * (n c : ℝ) - (B : ℝ) ≤ (L * n c - B : ℕ) := by
      have hn : L * n c ≤ (L * n c - B) + B := by omega
      have hr : (L : ℝ) * (n c : ℝ) ≤ (L * n c - B : ℕ) + (B : ℝ) := by exact_mod_cast hn
      linarith
    have hs : (L : ℝ) * (∑ c, n c : ℕ) - (Fintype.card χ : ℝ) * (B : ℝ) ≤
        ((∑ c, (L * n c - B) : ℕ) : ℝ) := by
      have hh := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset χ)) ↦ hlocal c)
      simpa only [Nat.cast_sum, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_const, card_univ, nsmul_eq_mul] using hh
    have hK : (0 : ℝ) < Fintype.card χ := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    have hr := real_floor_budget (∑ c, n c : ℕ) (Fintype.card χ : ℝ) (Nat.cast_nonneg _) hK
    have hB : (B : ℝ) = (L : ℝ) * ((L : ℝ) + 1) * ((L : ℝ) + 2) / 6 :=
      P3SurfaceDivisorLimits.cast_choose_shifted L
    change (2 / 3 : ℝ) * (∑ c, n c : ℕ) *
        Real.sqrt (2 * (∑ c, n c : ℕ) / (Fintype.card χ : ℝ)) - 3 * (∑ c, n c : ℕ) ≤
      ((∑ c, (L * n c - B) : ℕ) : ℝ)
    apply le_trans (b := (L : ℝ) * (∑ c, n c : ℕ) - (Fintype.card χ : ℝ) * (B : ℝ)) ?_ hs
    rw [hB]
    simpa only [L, cutoff, div_eq_mul_inv, mul_assoc] using hr

end PaperP1.CommonCutoffSurfaceBudget
