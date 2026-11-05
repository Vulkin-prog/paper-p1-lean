module

public import PaperP1.Arithmetic.DegreeUniformPrimeScale
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A cubic degree prime scale using the logarithmic prime supply

The prime threshold satisfies m log P ≤ 2P instead of the earlier m² ≤ P.
The constant is absolute and is chosen before the degree and box size.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicDegreePrimeScale

open DegreeUniformAffineParameters

theorem exists_scale (P₀ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
      ∃ P : ℕ, P₀ ≤ P ∧
        (avoidanceCount D N : ℝ) * Real.log P ≤ 2 * P ∧
        3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤ P ∧
        (P : ℝ) ≤ K * (D : ℝ) ^ 3 * (logarithmicBudget N : ℝ) ^ 2 *
          (N : ℝ) ^ (1 / (D : ℝ)) := by
  let M : ℝ := P₀ + 8192
  refine ⟨M ^ 2 + 1, by positivity, ?_⟩
  intro D N hD hDN
  let L := logarithmicBudget N
  let R := (N : ℝ) ^ (1 / (D : ℝ))
  let T := (D : ℝ) ^ 3 * (L : ℝ) ^ 2 * R
  let P := ⌈M ^ 2 * T⌉₊
  have hM : 8192 ≤ M := by dsimp [M]; have hp := Nat.cast_nonneg (α := ℝ) P₀; linarith only [hp]
  have hM0 : 0 < M := by linarith only [hM]
  have hM1 : 1 ≤ M := by linarith only [hM]
  have hN : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hDpos : (0 : ℝ) < D := by linarith only [hD1]
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hLpos : (0 : ℝ) < L := by linarith only [hL1]
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hT1 : 1 ≤ T := by
    have hd : (1 : ℝ) ≤ (D : ℝ) ^ 3 := one_le_pow₀ hD1
    have hl : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    have hdl : (1 : ℝ) ≤ (D : ℝ) ^ 3 * (L : ℝ) ^ 2 := by
      nlinarith only [hd, hl, mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hl)]
    exact hdl.trans (le_mul_of_one_le_right (by positivity) hR1)
  have hTpos : 0 < T := by linarith only [hT1]
  have hDpoly : (D : ℝ) ≤ (D : ℝ) ^ 3 * (L : ℝ) ^ 2 :=
    (le_self_pow₀ hD1 (by decide : 3 ≠ 0)).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1))
  have hDR : (D : ℝ) * R ≤ T := mul_le_mul_of_nonneg_right hDpoly (by positivity)
  have hceil : M ^ 2 * T ≤ (P : ℝ) := Nat.le_ceil _
  have hMlower : M ≤ M ^ 2 * T :=
    (le_self_pow₀ hM1 (by decide : 2 ≠ 0)).trans
      (le_mul_of_one_le_right (by positivity) hT1)
  have hP0 : P₀ ≤ P := by
    have hbase : (P₀ : ℝ) ≤ M := by dsimp [M]; linarith
    exact_mod_cast hbase.trans (hMlower.trans hceil)
  have hP1 : (1 : ℝ) ≤ P := hM1.trans (hMlower.trans hceil)
  have hPpos : (0 : ℝ) < P := by linarith only [hP1]
  have hupper : (P : ℝ) ≤ (M ^ 2 + 1) * T := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ M ^ 2 * T)).le
    change (P : ℝ) ≤ M ^ 2 * T + 1 at hh
    nlinarith only [hh, hT1]
  have hlogN := log_le_budget N hN
  have hlogD : Real.log (D : ℝ) ≤ L :=
    (Real.log_le_log hDpos (by exact_mod_cast hDN)).trans hlogN
  have hlogL : Real.log (L : ℝ) ≤ L :=
    (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hlogR : Real.log R ≤ L := by
    dsimp only [R]
    rw [Real.log_rpow hNpos]
    have hfrac : 1 / (D : ℝ) ≤ 1 := (div_le_one hDpos).mpr hD1
    have hh := mul_le_mul_of_nonneg_right hfrac (Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN))
    exact hh.trans (by simpa using hlogN)
  have hlogT : Real.log T ≤ 6 * L := by
    dsimp only [T]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    norm_num
    linarith only [hlogD, hlogL, hlogR]
  have hPupper : (P : ℝ) ≤ (M + 1) ^ 2 * T :=
    hupper.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hM0]) hTpos.le)
  have hlogM : Real.log (M + 1) ≤ M := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < M + 1)
    linarith only [hh]
  have hlogP : Real.log (P : ℝ) ≤ (2 * M + 6) * L := by
    have hh := Real.log_le_log hPpos hPupper
    rw [Real.log_mul (by positivity) hTpos.ne', Real.log_pow] at hh
    norm_num at hh
    have hML : M ≤ M * L := le_mul_of_one_le_right hM0.le hL1
    nlinarith only [hh, hlogM, hlogT, hML]
  have hm : (avoidanceCount D N : ℝ) ≤ 128 * (D : ℝ) ^ 3 * L := by
    exact_mod_cast avoidance_le D N hD
  have hcoefficient : 128 * (2 * M + 6) ≤ 2 * M ^ 2 := by
    nlinarith only [hM, sq_nonneg (M - 8192)]
  have hprime : 3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤ P := by
    have hroot := mul_le_mul_of_nonneg_left (DegreeUniformPrimeScale.box_root_bound D N hD)
      (by positivity : (0 : ℝ) ≤ 3 * Real.exp 1)
    have hexp : 6 * Real.exp 1 ≤ M ^ 2 := by
      nlinarith only [Real.exp_one_lt_three, hM, sq_nonneg (M - 8192)]
    calc
      _ ≤ (6 * Real.exp 1) * ((D : ℝ) * R) := by
        convert hroot using 1
        dsimp only [R]
        ring
      _ ≤ M ^ 2 * T := mul_le_mul hexp hDR (by positivity) (by positivity)
      _ ≤ _ := hceil
  refine ⟨P, hP0, ?_, hprime, ?_⟩
  · calc
      _ ≤ (128 * (D : ℝ) ^ 3 * L) * ((2 * M + 6) * L) :=
        mul_le_mul hm hlogP (Real.log_nonneg hP1) (by positivity)
      _ = (128 * (2 * M + 6)) * ((D : ℝ) ^ 3 * (L : ℝ) ^ 2) := by ring
      _ ≤ (2 * M ^ 2) * ((D : ℝ) ^ 3 * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ ≤ 2 * (M ^ 2 * T) := by
        have hh := le_mul_of_one_le_right
          (by positivity : 0 ≤ (D : ℝ) ^ 3 * (L : ℝ) ^ 2) hR1
        have hb := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * M ^ 2)
        simpa only [T, mul_assoc] using hb
      _ ≤ 2 * P := mul_le_mul_of_nonneg_left hceil (by norm_num)
  · simpa only [T, mul_assoc] using hupper

end PaperP1.LogarithmicDegreePrimeScale
