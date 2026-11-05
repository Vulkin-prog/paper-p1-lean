module

public import PaperP1.Analysis.ElementaryReciprocalPivotUpper
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # An internal exponential square-root-log upper bound for pivot reciprocals

The Rankin exponent and the cutoff both vary with the integer scale. Every
Euler factor and prefactor is controlled explicitly, without ordinary EIP.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareRootReciprocalUpper

open Finset Filter OddPrimePivot ReciprocalOddPivots PolylogPivotExceptions

theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hs : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  nlinarith only [hs, Real.exp_one_lt_three, Real.exp_pos (1 / 2 : ℝ)]

theorem linear_prefactor (t : ℝ) (ht : 16 ≤ t) : 3 * t / 2 ≤ Real.exp (t / 2) := by
  have hbase := Real.add_one_le_exp (t / 4)
  have hpow := pow_le_pow_left₀ (by linarith only [ht] : 0 ≤ t / 4 + 1) hbase 2
  have heq : Real.exp (t / 4) ^ 2 = Real.exp (t / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [heq] at hpow
  nlinarith only [hpow, ht, mul_nonneg (by linarith only [ht] : 0 ≤ t - 16) (by linarith only [ht] : 0 ≤ t)]

theorem small_pivot_bound {N Y : ℕ} (hN : 2 ≤ N)
    (ht : 4 ≤ Real.sqrt (Real.log N)) (hY : 1 ≤ Y)
    (hcut : (Y : ℝ) ≤ Real.exp (Real.sqrt (Real.log N) / 4)) :
    ((pivotValues (3 * N) Y).card : ℝ) ≤
      (3 * Real.sqrt (Real.log N) / 2) * N * Real.exp (-Real.sqrt (Real.log N)) := by
  let t := Real.sqrt (Real.log N)
  let σ := 1 - 2 / t
  have htpos : 0 < t := by linarith only [ht]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsq : t ^ 2 = Real.log N := Real.sq_sqrt (Real.log_nonneg hn1)
  have hfrac : 2 / t ≤ 1 / 2 := (div_le_iff₀ htpos).mpr (by linarith only [ht])
  have hfracpos : 0 < 2 / t := by positivity
  have hσ : 1 / 2 ≤ σ := by dsimp only [σ]; linarith only [hfrac]
  have hσ1 : σ < 1 := by dsimp only [σ]; linarith only [hfracpos]
  have hδ : 1 - σ = 2 / t := by dsimp only [σ]; ring
  have hinv : 1 / (1 - σ) = t / 2 := by rw [hδ]; field_simp
  have hy : (Y : ℝ) ^ (1 - σ) ≤ 2 := by
    calc
      _ ≤ (Real.exp (t / 4)) ^ (1 - σ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg Y) hcut (by linarith only [hσ1])
      _ = Real.exp (1 / 2 : ℝ) := by
        rw [← Real.exp_mul, hδ]
        congr 1
        field_simp
        ring
      _ ≤ _ := exp_half_le_two
  have heuler : (Y : ℝ) ^ (1 - σ) / (1 - σ) ≤ t := by
    rw [div_eq_mul_inv, ← one_div, hinv]
    nlinarith only [hy, htpos]
  have hdiv : Real.log (N : ℝ) / t = t := (div_eq_iff htpos.ne').mpr (by nlinarith only [hsq])
  have hNpow : (N : ℝ) ^ σ = (N : ℝ) * Real.exp (-2 * t) := by
    rw [Real.rpow_def_of_pos hn]
    have hid : Real.log (N : ℝ) * σ = Real.log N + -2 * t := by
      dsimp only [σ]
      rw [show Real.log (N : ℝ) * (1 - 2 / t) = Real.log N - 2 * (Real.log N / t) by ring, hdiv]
      ring
    rw [hid, Real.exp_add, Real.exp_log hn]
  have hthree : ((3 * N : ℕ) : ℝ) ^ σ ≤ 3 * (N : ℝ) ^ σ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hn.le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hσ1.le) (Real.rpow_nonneg hn.le _)
  have hb := pivot_count_rankin (3 * N) Y hY σ hσ hσ1
  rw [hinv] at hb
  have hbound : ((pivotValues (3 * N) Y).card : ℝ) ≤
      (3 * ((N : ℝ) * Real.exp (-2 * t))) * (t / 2) * Real.exp t := by
    apply hb.trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (by simpa only [hNpow] using hthree) (by positivity))
      (Real.exp_le_exp.mpr heuler) (Real.exp_nonneg _) (by positivity)
  have heq : (3 * ((N : ℝ) * Real.exp (-2 * t))) * (t / 2) * Real.exp t =
      (3 * t / 2) * N * Real.exp (-t) := by
    calc
      _ = (3 * t / 2) * N * (Real.exp (-2 * t) * Real.exp t) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  exact hbound.trans_eq heq

theorem finite_upper {N : ℕ} (hN : 2 ≤ N) (ht : 160 ≤ Real.sqrt (Real.log N)) :
    pivotSum (3 * N) + 1 ≤ (N : ℝ) * Real.exp (-Real.sqrt (Real.log N) / 5) := by
  let t := Real.sqrt (Real.log N)
  let Y := ⌊Real.exp (t / 4)⌋₊
  have htpos : 0 < t := by linarith only [ht]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsq : t ^ 2 = Real.log N := Real.sq_sqrt (Real.log_nonneg hn1)
  have hexp : 2 ≤ Real.exp (t / 4) := by
    have hh := Real.add_one_le_exp (t / 4)
    linarith only [hh, ht]
  have hYupper : (Y : ℝ) ≤ Real.exp (t / 4) := Nat.floor_le (Real.exp_nonneg _)
  have hYhalf : Real.exp (t / 4) ≤ 2 * (Y : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp (t / 4))
    change Real.exp (t / 4) < (Y : ℝ) + 1 at hh
    linarith only [hh, hexp]
  have hYpos : 0 < Y := by
    have hh : (0 : ℝ) < Y := by linarith only [hYhalf, hexp]
    exact_mod_cast hh
  have hsmall : ((pivotValues (3 * N) Y).card : ℝ) ≤ (N : ℝ) * Real.exp (-t / 2) := by
    have hc := small_pivot_bound hN (by linarith only [ht]) (by omega) hYupper
    have hh := mul_le_mul_of_nonneg_right (linear_prefactor t (by linarith only [ht]))
      (by positivity : 0 ≤ (N : ℝ) * Real.exp (-t))
    have hid : Real.exp (t / 2) * ((N : ℝ) * Real.exp (-t)) = (N : ℝ) * Real.exp (-t / 2) := by
      calc
        _ = (N : ℝ) * (Real.exp (t / 2) * Real.exp (-t)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring
    rw [hid] at hh
    change ((pivotValues (3 * N) Y).card : ℝ) ≤ (3 * t / 2) * N * Real.exp (-t) at hc
    nlinarith only [hc, hh]
  have hinv : 1 / (Y : ℝ) ≤ 2 * Real.exp (-t / 4) := by
    rw [show -t / 4 = -(t / 4) by ring, Real.exp_neg]
    change 1 / (Y : ℝ) ≤ 2 / Real.exp (t / 4)
    exact (div_le_div_iff₀ (by exact_mod_cast hYpos : (0 : ℝ) < Y) (Real.exp_pos _)).mpr
      (by simpa only [one_mul] using hYhalf)
  have htail : ((3 * N : ℕ) : ℝ) / Y ≤ 6 * N * Real.exp (-t / 4) := by
    have hh := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 3 * N)
    push_cast
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith only [hh]
  have hsmall' : ((pivotValues (3 * N) Y).card : ℝ) ≤ (N : ℝ) * Real.exp (-t / 4) :=
    hsmall.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [htpos])) hn.le)
  have hone : 1 ≤ (N : ℝ) * Real.exp (-t / 4) := by
    have he : (N : ℝ) * Real.exp (-t / 4) = Real.exp (Real.log N + -t / 4) := by
      rw [Real.exp_add, Real.exp_log hn]
    rw [he]
    exact Real.one_le_exp (by nlinarith only [hsq, ht])
  have hfinite := ElementaryReciprocalPivotUpper.finite_cutoff (3 * N) Y (by omega)
  have hsum : pivotSum (3 * N) + 1 ≤ 8 * N * Real.exp (-t / 4) := by
    linarith only [hfinite, hsmall', htail, hone]
  have hpref : 8 ≤ Real.exp (t / 20) := by
    have hh := Real.add_one_le_exp (t / 20)
    linarith only [hh, ht]
  calc
    _ ≤ 8 * N * Real.exp (-t / 4) := hsum
    _ ≤ Real.exp (t / 20) * N * Real.exp (-t / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref hn.le) (Real.exp_nonneg _)
    _ = (N : ℝ) * (Real.exp (t / 20) * Real.exp (-t / 4)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem uniform_upper : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    pivotSum (3 * N) + 1 ≤ (N : ℝ) * Real.exp (-Real.sqrt (Real.log N) / 5) := by
  have ht : Tendsto (fun N : ℕ ↦ Real.sqrt (Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, h⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (160 : ℝ)))
  exact ⟨N₀, fun N hN ↦ finite_upper (by omega) (h N (by omega))⟩

end PaperP1.SquareRootReciprocalUpper
