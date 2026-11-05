module

public import PaperP1.Arithmetic.BoundedProductFibres
public import PaperP1.Arithmetic.ReciprocalOddPivots
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # An elementary lower bound for full reciprocal pivot sums

Bounded products fill a power-size population after the divisor multiplicities
are paid. This establishes the power-scale lower bound without the fine EIP law.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ElementaryReciprocalPrimeLower

open Finset Filter BoundedProductFibres OddPrimePivot ReciprocalOddPivots

theorem fixed_order (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      c * (N : ℝ) ^ (1 - 1 / (k : ℝ) - δ) ≤ pivotSum N := by
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually 1 (δ / k) (by positivity)
  have hrootT : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 / (k : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (k : ℝ))).comp tendsto_natCast_atTop_atTop
  obtain ⟨NR, hr⟩ := eventually_atTop.mp (hrootT.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨(1 / 2 : ℝ) ^ (k - 1), by positivity, max 2 (max ND NR), by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let R := (N : ℝ) ^ (1 / (k : ℝ))
  let Y := ⌊R⌋₊
  let I := Icc 1 Y
  have hR : 2 ≤ R := hr N (by omega)
  have hYupper : (Y : ℝ) ≤ R := Nat.floor_le (by positivity)
  have hYlower : R / 2 ≤ (Y : ℝ) := by
    have hh := Nat.lt_floor_add_one R
    change R < (Y : ℝ) + 1 at hh
    linarith only [hh, hR]
  have hYpos : 0 < Y := by
    have hh : (0 : ℝ) < Y := by linarith only [hYlower, hR]
    exact_mod_cast hh
  have hRpow : R ^ k = (N : ℝ) := by
    simpa only [R, one_div] using (Real.rpow_inv_natCast_pow (n := k) hn.le (by omega))
  have hYpow : Y ^ k ≤ N := by
    have hh := (pow_le_pow_left₀ (Nat.cast_nonneg Y) hYupper k).trans_eq hRpow
    exact_mod_cast hh
  have hvalues (n : ℕ) (hnI : n ∈ (tuples k I).image value) : 0 < n ∧ n ≤ N := by
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hnI
    have hpoint := fun i ↦ mem_Icc.mp (Fintype.mem_piFinset.mp hx i)
    refine ⟨prod_pos (fun i _ ↦ (hpoint i).1), ?_⟩
    have hh : value x ≤ Y ^ k := by
      calc
        _ ≤ ∏ _i : Fin k, Y := prod_le_prod (fun i _ ↦ (hpoint i).2)
        _ = _ := by simp
    exact hh.trans hYpow
  have hdiv (n : ℕ) (hnI : n ∈ (tuples k I).image value) :
      (n.divisors.card : ℝ) ^ k ≤ (N : ℝ) ^ δ := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg n.divisors.card)
      (hd N (by omega) n (by simpa using (hvalues n hnI).2)) k
    rw [← Real.rpow_mul_natCast hn.le, div_mul_cancel₀ δ hkR.ne'] at hh
    exact hh
  have hrec := reciprocal_lower k Y I (by omega)
    (fun a ha ↦ mem_Icc.mp ha) ((N : ℝ) ^ δ) (by positivity) hdiv
  have hsub : (tuples k I).image value ⊆ Icc 1 N := by
    intro n hnI
    exact mem_Icc.mpr (hvalues n hnI)
  have hsum : (∑ n ∈ (tuples k I).image value, 1 / (largestOddPrime n : ℝ)) ≤ pivotSum N :=
    sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
  have hYcard : I.card = Y := by simp only [I, Nat.card_Icc]; omega
  rw [hYcard] at hrec
  have hfull : (Y : ℝ) ^ k ≤ (N : ℝ) ^ δ * Y * pivotSum N :=
    hrec.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hcancel : (Y : ℝ) ^ (k - 1) ≤ (N : ℝ) ^ δ * pivotSum N := by
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ) < Y by exact_mod_cast hYpos)).mp
    calc
      _ = (Y : ℝ) ^ k := by rw [← pow_succ]; congr 1; omega
      _ ≤ _ := hfull
      _ = _ := by ring
  have hfloor := (pow_le_pow_left₀ (by positivity : 0 ≤ R / 2) hYlower (k - 1)).trans hcancel
  have hpower : (R / 2) ^ (k - 1) =
      (1 / 2 : ℝ) ^ (k - 1) * (N : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    rw [div_eq_mul_inv, mul_pow]
    dsimp only [R]
    rw [← Real.rpow_mul_natCast hn.le]
    have he : 1 / (k : ℝ) * ((k - 1 : ℕ) : ℝ) = 1 - 1 / (k : ℝ) := by
      rw [Nat.cast_sub hk, Nat.cast_one]
      field_simp
    rw [he]
    ring
  rw [hpower] at hfloor
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hn δ)).mp
  calc
    _ = (1 / 2 : ℝ) ^ (k - 1) * (N : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ _ := hfloor
    _ = _ := by ring

theorem uniform_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, (N : ℝ) ^ (1 - ε) ≤ pivotSum N := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (4 / ε))
  have hk1 : 1 ≤ k := by have hh := (le_max_left _ _).trans_lt hk; exact_mod_cast hh.le
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hfrac : 1 / (k : ℝ) ≤ ε / 4 := by
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hk)
    apply (div_le_iff₀ hkpos).mpr
    nlinarith only [hh]
  obtain ⟨c, hc, NF, hNF, hf⟩ := fixed_order k hk1 (ε / 4) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (1 / c) (1 - ε) (ε / 2) (by positivity)
  refine ⟨max NF NA, by omega, ?_⟩
  intro N hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsmall : (1 / c) * (N : ℝ) ^ (1 - ε) ≤
      (N : ℝ) ^ (1 - 1 / (k : ℝ) - ε / 4) :=
    (ha N (by omega)).trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hfrac]))
  have hh := mul_le_mul_of_nonneg_left hsmall hc.le
  have hid : c * ((1 / c) * (N : ℝ) ^ (1 - ε)) = (N : ℝ) ^ (1 - ε) := by field_simp
  rw [hid] at hh
  exact hh.trans (hf N (by omega))

end PaperP1.ElementaryReciprocalPrimeLower
