module

public import PaperP1.Asymptotics.ArbitraryPolylogPivotCount
public import PaperP1.Arithmetic.ReciprocalOddPivots
public import PaperP1.Arithmetic.DyadicOddPivots
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Reciprocal pivot sums beat every fixed logarithmic power internally

Rankin controls the actual small-pivot population at a higher fixed
logarithmic cutoff. Large pivots pay their reciprocal directly.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementaryReciprocalPivotUpper

open Finset Filter OddPrimePivot ReciprocalOddPivots

theorem finite_cutoff (X Y : ℕ) (hY : 1 ≤ Y) :
    pivotSum X ≤ (pivotValues X Y).card + (X : ℝ) / Y := by
  let A := pivotValues X Y
  let B := (Icc 1 X).filter (fun n ↦ ¬ largestOddPrime n ≤ Y)
  have hA : (∑ n ∈ A, 1 / (largestOddPrime n : ℝ)) ≤ A.card := by
    calc
      _ ≤ ∑ _n ∈ A, (1 : ℝ) := sum_le_sum (fun n _ ↦ by
        simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by exact_mod_cast largestOddPrime_pos n : (1 : ℝ) ≤ largestOddPrime n))
      _ = _ := by simp
  have hBcard : (B.card : ℝ) ≤ X := by
    exact_mod_cast (card_le_card (filter_subset _ _)).trans_eq (by simp : (Icc 1 X).card = X)
  have hB : (∑ n ∈ B, 1 / (largestOddPrime n : ℝ)) ≤ (X : ℝ) / Y := by
    calc
      _ ≤ ∑ _n ∈ B, 1 / (Y : ℝ) := sum_le_sum (fun n hn ↦
        one_div_le_one_div_of_le (by exact_mod_cast (show 0 < Y by omega))
          (by exact_mod_cast (show Y ≤ largestOddPrime n by have hh := (mem_filter.mp hn).2; omega)))
      _ = (B.card : ℝ) / Y := by simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv, one_mul]
      _ ≤ _ := div_le_div_of_nonneg_right hBcard (Nat.cast_nonneg Y)
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 X)
    (fun n ↦ largestOddPrime n ≤ Y) (fun n ↦ 1 / (largestOddPrime n : ℝ))
  change (∑ n ∈ A, 1 / (largestOddPrime n : ℝ)) +
    (∑ n ∈ B, 1 / (largestOddPrime n : ℝ)) = pivotSum X at hsplit
  linarith only [hA, hB, hsplit]

theorem uniform_logarithmic_upper (A : ℕ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log N ^ A * (pivotSum (3 * N) + 1) ≤ N := by
  let m := A + 1
  have hm : 1 ≤ m := by dsimp [m]; omega
  let σ := ArbitraryPolylogPivotCount.exponent m
  obtain ⟨hσ, hσ1⟩ := ArbitraryPolylogPivotCount.exponent_bounds m hm
  let p := σ + (1 - σ) / 2
  have hp0 : 0 ≤ p := by dsimp [p, σ]; linarith only [hσ, hσ1]
  have hp1 : p < 1 := by dsimp [p, σ]; linarith only [hσ1]
  obtain ⟨NC, _hNC, hc⟩ := ArbitraryPolylogPivotCount.uniform_value_bound m hm
    ((1 - σ) / 2) (by dsimp only [σ]; linarith only [hσ1])
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NL, hl⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop (12 : ℝ)))
  have hsmallT := (isLittleO_log_rpow_rpow_atTop (A : ℝ) (by linarith only [hp1] : 0 < 1 - p)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NS, hs⟩ := eventually_atTop.mp (hsmallT.bound (by norm_num : (0 : ℝ) < 1 / 4))
  refine ⟨2 + NC + NL + NS, by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog12 := hl N (by omega)
  have hlog : 0 < Real.log N := by linarith only [hlog12]
  have hlog1 : 1 ≤ Real.log N := by linarith only [hlog12]
  let Y := ⌊Real.log N ^ m⌋₊
  have hlogm : 2 ≤ Real.log N ^ m :=
    (by linarith only [hlog12] : (2 : ℝ) ≤ Real.log N).trans (le_self_pow₀ hlog1 (by omega))
  have hYupper : (Y : ℝ) ≤ Real.log N ^ m := Nat.floor_le (by positivity)
  have hYhalf : Real.log N ^ m ≤ 2 * (Y : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.log N ^ m)
    change Real.log N ^ m < (Y : ℝ) + 1 at hh
    linarith only [hh, hlogm]
  have hYpos : 0 < Y := by
    have hh : (0 : ℝ) < Y := by linarith only [hYhalf, hlogm]
    exact_mod_cast hh
  have hcount := hc N (by omega) Y (by omega) hYupper
  change ((pivotValues (3 * N) Y).card : ℝ) ≤ (N : ℝ) ^ p at hcount
  have htail : ((3 * N : ℕ) : ℝ) / Y ≤ 6 * N / Real.log N ^ m := by
    push_cast
    apply (div_le_div_iff₀ (by exact_mod_cast hYpos : (0 : ℝ) < Y) (by positivity : 0 < Real.log N ^ m)).mpr
    have hh := mul_le_mul_of_nonneg_left hYhalf (by positivity : (0 : ℝ) ≤ 3 * N)
    nlinarith only [hh]
  have hfull := finite_cutoff (3 * N) Y (by omega)
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ p := Real.one_le_rpow hn1 hp0
  have hsum : pivotSum (3 * N) + 1 ≤ 2 * (N : ℝ) ^ p + 6 * N / Real.log N ^ m := by
    linarith only [hfull, hcount, htail, hone]
  have hlogsmall : Real.log N ^ A ≤ (1 / 4) * (N : ℝ) ^ (1 - p) := by
    have hh := hs N (by omega)
    simpa only [Function.comp_apply, Real.norm_eq_abs, Real.rpow_natCast, abs_of_nonneg (by positivity : 0 ≤ Real.log N ^ A),
      abs_of_nonneg (Real.rpow_nonneg hn.le (1 - p))] using hh
  have hfirst : Real.log N ^ A * (2 * (N : ℝ) ^ p) ≤ (N : ℝ) / 2 := by
    calc
      _ ≤ ((1 / 4) * (N : ℝ) ^ (1 - p)) * (2 * (N : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_right hlogsmall (by positivity)
      _ = (N : ℝ) / 2 := by
        rw [show ((1 / 4 : ℝ) * (N : ℝ) ^ (1 - p)) * (2 * (N : ℝ) ^ p) =
          (1 / 2 : ℝ) * ((N : ℝ) ^ (1 - p) * (N : ℝ) ^ p) by ring,
          ← Real.rpow_add hn, sub_add_cancel, Real.rpow_one]
        ring
  have hsecond : Real.log N ^ A * (6 * (N : ℝ) / Real.log N ^ m) ≤ (N : ℝ) / 2 := by
    have hid : Real.log N ^ A * (6 * (N : ℝ) / Real.log N ^ m) = 6 * N / Real.log N := by
      dsimp only [m]
      rw [pow_succ]
      field_simp
    rw [hid]
    exact (div_le_iff₀ hlog).mpr (by nlinarith only [hlog12, hn])
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ Real.log N ^ A)
  nlinarith only [hh, hfirst, hsecond]

theorem dyadic_logarithmic_upper (A : ℕ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      Real.log N ^ A * (DyadicOddPivots.dyadicSum N + 1) ≤ N := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_logarithmic_upper A
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hsub : Ico N (2 * N) ⊆ Icc 1 (3 * N) := by
    intro n hn
    obtain ⟨hl, hu⟩ := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum : DyadicOddPivots.dyadicSum N ≤ pivotSum (3 * N) :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have hsum' : DyadicOddPivots.dyadicSum N + 1 ≤ pivotSum (3 * N) + 1 := by linarith only [hsum]
  exact (mul_le_mul_of_nonneg_left hsum'
    (by have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        exact pow_nonneg (Real.log_nonneg hn1) A)).trans (h N hN)

end PaperP1.ElementaryReciprocalPivotUpper
