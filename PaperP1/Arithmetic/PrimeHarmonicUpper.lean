module

public import PaperP1.Arithmetic.WeightedPrimeSum
public import PaperP1.Arithmetic.PolylogPivotExceptions
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A finite harmonic prime bound retained in the Rankin Euler factor

The elementary primorial bound and a logarithmic integral control the
prime reciprocals. No Mertens theorem or reciprocal-prime asymptotic is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeHarmonicUpper

open Finset DefectCounting WeightedPrimeSum MeasureTheory

def weight (n : ℕ) : ℝ := ((max 2 n : ℕ) : ℝ)⁻¹ / Real.log ((max 2 n : ℕ) : ℝ)

theorem reciprocal_log_antitone :
    AntitoneOn (fun x : ℝ ↦ x⁻¹ / Real.log x) (Set.Ici 2) := by
  intro x hx y _hy hxy
  have hxpos : 0 < x := by have hh : (2 : ℝ) ≤ x := hx; linarith only [hh]
  have hlogx : 0 < Real.log x := Real.log_pos (by have hh : (2 : ℝ) ≤ x := hx; linarith only [hh])
  have hinv : y⁻¹ ≤ x⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hxpos hxy
  calc
    _ ≤ y⁻¹ / Real.log x := div_le_div_of_nonneg_left
      (inv_nonneg.mpr (hxpos.le.trans hxy)) hlogx (Real.log_le_log hxpos hxy)
    _ ≤ _ := div_le_div_of_nonneg_right hinv hlogx.le

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  have hm : (1 : ℝ) ≤ ((max 2 n : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ max 2 n by omega)
  exact div_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Real.log_nonneg hm)

theorem weight_antitone : Antitone weight := by
  intro i j hij
  apply reciprocal_log_antitone
  · change (2 : ℝ) ≤ ((max 2 i : ℕ) : ℝ)
    exact_mod_cast le_max_left 2 i
  · change (2 : ℝ) ≤ ((max 2 j : ℕ) : ℝ)
    exact_mod_cast le_max_left 2 j
  · exact_mod_cast max_le_max (le_refl 2) hij

theorem weight_prime (p : ℕ) (hp : p.Prime) : Real.log p * weight p = 1 / (p : ℝ) := by
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  dsimp only [weight]
  rw [max_eq_right hp.two_le]
  field_simp

theorem shifted_sum_bound (Y : ℕ) :
    (∑ i ∈ range Y, weight (i + 1)) ≤
      2 * weight 2 + Real.log (Real.log ((Y : ℝ) + 2)) - Real.log (Real.log 2) := by
  have henlarge : (∑ i ∈ range Y, weight (i + 1)) ≤ ∑ i ∈ range (Y + 2), weight (i + 1) :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ ↦ weight_nonneg (i + 1))
  have hsplit : (∑ i ∈ range (Y + 2), weight (i + 1)) =
      2 * weight 2 + ∑ i ∈ range Y, (2 + (i + 1 : ℕ) : ℝ)⁻¹ / Real.log (2 + (i + 1 : ℕ) : ℝ) := by
    rw [show Y + 2 = 2 + Y by omega, sum_range_add]
    have hhead : (∑ i ∈ range 2, weight (i + 1)) = 2 * weight 2 := by
      norm_num [sum_range_succ, weight, two_mul]
    rw [hhead]
    congr 1
    apply sum_congr rfl
    intro i _hi
    dsimp only [weight]
    rw [max_eq_right (by omega : 2 ≤ 2 + i + 1)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc]
  have hanti : AntitoneOn (fun x : ℝ ↦ x⁻¹ / Real.log x) (Set.Icc 2 (2 + (Y : ℝ))) :=
    reciprocal_log_antitone.mono (fun _ hx ↦ hx.1)
  have hint := hanti.sum_le_integral
  rw [integral_inv_div_log (by norm_num : (1 : ℝ) < 2) (by have hh := Nat.cast_nonneg (α := ℝ) Y; linarith only [hh] : (1 : ℝ) < 2 + Y)] at hint
  have hsum : (∑ i ∈ range Y, (2 + (i + 1 : ℕ) : ℝ)⁻¹ / Real.log (2 + (i + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log ((Y : ℝ) + 2)) - Real.log (Real.log 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_comm] using hint
  linarith only [henlarge, hsplit, hsum]

theorem harmonic_upper (Y : ℕ) :
    (∑ p ∈ smallPrimesUpTo Y, 1 / (p : ℝ)) ≤
      Real.log 4 * (2 * weight 2 + Real.log (Real.log ((Y : ℝ) + 2)) - Real.log (Real.log 2)) := by
  have hh := sum_log_prime_mul_le Y weight (fun i ↦ weight_nonneg (i + 1))
    (fun i j hij ↦ weight_antitone (Nat.add_le_add_right hij 1))
  have hleft : (∑ p ∈ smallPrimesUpTo Y, Real.log p * weight p) =
      ∑ p ∈ smallPrimesUpTo Y, 1 / (p : ℝ) :=
    sum_congr rfl (fun p hp ↦ weight_prime p (mem_smallPrimesUpTo.mp hp).1)
  rw [hleft] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (shifted_sum_bound Y) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)))

def constant : ℝ := Real.log 4 * (2 * weight 2 + |Real.log (Real.log 2)| + 2)

theorem constant_pos : 0 < constant := by
  have hw := weight_nonneg 2
  have ha := abs_nonneg (Real.log (Real.log 2))
  exact mul_pos (Real.log_pos (by norm_num)) (by linarith only [hw, ha])

theorem harmonic_uniform (Y : ℕ) (hY : 2 ≤ Y) :
    (∑ p ∈ smallPrimesUpTo Y, 1 / (p : ℝ)) ≤
      constant * (1 + Real.log (Real.log ((Y : ℝ) + 2))) := by
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hinner : 1 ≤ Real.log ((Y : ℝ) + 2) := by
    have hh := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ (Y : ℝ) + 2 by
        have hy : (2 : ℝ) ≤ Y := by exact_mod_cast hY
        linarith only [hy, Real.exp_one_lt_three])
    simpa only [Real.log_exp] using hh
  have houter := Real.log_nonneg hinner
  have hw := weight_nonneg 2
  have ha := abs_nonneg (Real.log (Real.log 2))
  have hbase : Real.log 4 * (2 * weight 2 - Real.log (Real.log 2)) ≤ constant := by
    dsimp only [constant]
    exact mul_le_mul_of_nonneg_left (by linarith only [neg_le_abs (Real.log (Real.log 2))]) hlog4.le
  have hcoef : Real.log 4 ≤ constant := by
    dsimp only [constant]
    nlinarith only [hw, ha, hlog4]
  calc
    _ ≤ Real.log 4 * (2 * weight 2 + Real.log (Real.log ((Y : ℝ) + 2)) - Real.log (Real.log 2)) := harmonic_upper Y
    _ = Real.log 4 * (2 * weight 2 - Real.log (Real.log 2)) +
        Real.log 4 * Real.log (Real.log ((Y : ℝ) + 2)) := by ring
    _ ≤ constant + constant * Real.log (Real.log ((Y : ℝ) + 2)) :=
      add_le_add hbase (mul_le_mul_of_nonneg_right hcoef houter)
    _ = _ := by ring

theorem weighted_prime_uniform (Y : ℕ) (hY : 2 ≤ Y) (σ : ℝ) (hσ : σ ≤ 1) :
    WeightedPrimeSum.primeSum Y σ ≤
      constant * (Y : ℝ) ^ (1 - σ) * (1 + Real.log (Real.log ((Y : ℝ) + 2))) := by
  have hterm (p : ℕ) (hp : p ∈ smallPrimesUpTo Y) :
      (p : ℝ) ^ (-σ) ≤ (Y : ℝ) ^ (1 - σ) * (1 / (p : ℝ)) := by
    have hdata := mem_smallPrimesUpTo.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hdata.1.pos
    calc
      _ = (p : ℝ) ^ (1 - σ) * (p : ℝ) ^ (-1 : ℝ) := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      _ ≤ (Y : ℝ) ^ (1 - σ) * (p : ℝ) ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le
          (by exact_mod_cast hdata.2) (by linarith only [hσ])) (Real.rpow_nonneg hp0.le _)
      _ = _ := by rw [Real.rpow_neg_one, one_div]
  calc
    _ ≤ ∑ p ∈ smallPrimesUpTo Y, (Y : ℝ) ^ (1 - σ) * (1 / (p : ℝ)) := sum_le_sum hterm
    _ = (Y : ℝ) ^ (1 - σ) * ∑ p ∈ smallPrimesUpTo Y, 1 / (p : ℝ) := (mul_sum _ _ _).symm
    _ ≤ (Y : ℝ) ^ (1 - σ) * (constant * (1 + Real.log (Real.log ((Y : ℝ) + 2)))) :=
      mul_le_mul_of_nonneg_left (harmonic_uniform Y hY) (Real.rpow_nonneg (Nat.cast_nonneg Y) _)
    _ = _ := by ring

theorem euler_uniform (Y : ℕ) (hY : 2 ≤ Y) (σ : ℝ) (hσ : σ ≤ 1) :
    SmallKernelCount.eulerProduct Y σ ≤
      Real.exp (constant * (Y : ℝ) ^ (1 - σ) * (1 + Real.log (Real.log ((Y : ℝ) + 2)))) := by
  apply (Real.prod_one_add_le_exp_sum (smallPrimesUpTo Y)
    (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) (-σ))).trans
  exact Real.exp_le_exp.mpr (weighted_prime_uniform Y hY σ hσ)

theorem pivot_count_uniform (X Y : ℕ) (hY : 2 ≤ Y) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ((OddPrimePivot.pivotValues X Y).card : ℝ) ≤ (X : ℝ) ^ σ *
      Real.exp (constant * (Y : ℝ) ^ (1 - σ) * (1 + Real.log (Real.log ((Y : ℝ) + 2)))) := by
  have hsub : ((OddPrimePivot.pivotValues X Y).card : ℝ) ≤ (SmallKernelCount.smallKernelValues Y 1 X).card := by
    exact_mod_cast Finset.card_le_card (PolylogPivotExceptions.pivot_subset_small_kernel X Y (by omega))
  have hbase := SmallKernelCount.card_smallKernelValues_le_euler Y 1 X σ hσ
  have hone : PartialPowerSum.powerSum σ 1 = 1 := by simp [PartialPowerSum.powerSum]
  rw [hone, mul_one] at hbase
  exact hsub.trans (hbase.trans (mul_le_mul_of_nonneg_left (euler_uniform Y hY σ hσ1)
    (Real.rpow_nonneg (Nat.cast_nonneg X) _)))

end PaperP1.PrimeHarmonicUpper
