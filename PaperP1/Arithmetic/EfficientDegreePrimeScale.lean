module

public import PaperP1.Arithmetic.DegreeUniformPrimeScale

/-! # A redundant prime scale with a logarithmic height allowance

The avoidance multiplicity is selected after the prime scale, using log(P).
This removes one logarithmic factor without changing the height budget.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EfficientDegreePrimeScale

open DegreeUniformAffineParameters

theorem log_le_half (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < x / 2)
  rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
  have htwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [ht]
  linarith only [hh, htwo]

theorem exists_scale (P₀ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
      ∃ P m : ℕ, P₀ ≤ P ∧ 1 ≤ m ∧ (m : ℝ) * Real.log P ≤ P ∧
        N ^ (64 * D ^ 3) < P ^ m ∧
        3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤ P ∧
        3 * Real.exp 4 ≤ P ∧
        (P : ℝ) ≤ K * (D : ℝ) ^ 3 * (logarithmicBudget N : ℝ) * (N : ℝ) ^ (1 / (D : ℝ)) := by
  let M : ℝ := P₀ + (⌈3 * Real.exp 4⌉₊ : ℝ) + 8192
  have hM : 8192 ≤ M := by
    have hp := Nat.cast_nonneg (α := ℝ) P₀
    have hc := Nat.cast_nonneg (α := ℝ) ⌈3 * Real.exp 4⌉₊
    dsimp only [M]
    linarith only [hp, hc]
  have hM0 : 0 < M := by linarith only [hM]
  have hM1 : 1 ≤ M := by linarith only [hM]
  have hMP : (P₀ : ℝ) ≤ M := by
    have hc := Nat.cast_nonneg (α := ℝ) ⌈3 * Real.exp 4⌉₊
    dsimp only [M]
    linarith only [hc]
  have hMC : 3 * Real.exp 4 ≤ M := by
    have hh := Nat.le_ceil (3 * Real.exp 4)
    have hp := Nat.cast_nonneg (α := ℝ) P₀
    dsimp only [M]
    linarith only [hh, hp]
  refine ⟨M + 1, by positivity, ?_⟩
  intro D N hD hDN
  let L := logarithmicBudget N
  let R := (N : ℝ) ^ (1 / (D : ℝ))
  let T := (D : ℝ) ^ 3 * (L : ℝ) * R
  let P := ⌈M * T⌉₊
  have hN : 1 ≤ N := by omega
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := by linarith only [hn]
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR : 1 ≤ R := Real.one_le_rpow hn.le (by positivity)
  have hT1 : 1 ≤ T := by
    have hdc : (1 : ℝ) ≤ (D : ℝ) ^ 3 := one_le_pow₀ hd
    have hh : (1 : ℝ) ≤ (D : ℝ) ^ 3 * L := by nlinarith only [hdc, hL, mul_nonneg (sub_nonneg.mpr hdc) (sub_nonneg.mpr hL)]
    exact hh.trans (le_mul_of_one_le_right (by positivity) hR)
  have hceil : M * T ≤ (P : ℝ) := Nat.le_ceil _
  have hMPbound : M ≤ (P : ℝ) :=
    (le_mul_of_one_le_right hM0.le hT1).trans hceil
  have hP0 : P₀ ≤ P := by exact_mod_cast hMP.trans hMPbound
  have hp1 : (1 : ℝ) < P := by linarith only [hMPbound, hM]
  have hp0 : (0 : ℝ) < P := by linarith only [hp1]
  have hlogP : 0 < Real.log P := Real.log_pos hp1
  let A := 65 * (D : ℝ) ^ 3 * Real.log N
  let m := ⌈A / Real.log P⌉₊
  have hlogNpos : 0 < Real.log N := Real.log_pos hn
  have hA : 0 < A := by dsimp only [A]; positivity
  have hm : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hmhi : (m : ℝ) ≤ A / Real.log P + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmlo : A ≤ (m : ℝ) * Real.log P := (div_le_iff₀ hlogP).mp (Nat.le_ceil (A / Real.log P))
  have hlogN : Real.log N ≤ (L : ℝ) := log_le_budget N hN
  have h130 : 130 * (D : ℝ) ^ 3 * L ≤ (P : ℝ) := by
    have hTbase : (D : ℝ) ^ 3 * L ≤ T := le_mul_of_one_le_right (by positivity) hR
    have hM130 : (130 : ℝ) ≤ M := by linarith only [hM]
    have hh := mul_le_mul hM130 hTbase (by positivity) hM0.le
    exact (by nlinarith only [hh] : 130 * (D : ℝ) ^ 3 * L ≤ M * T).trans hceil
  have hAhalf : A ≤ (P : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_left hlogN (by positivity : (0 : ℝ) ≤ 65 * (D : ℝ) ^ 3)
    dsimp only [A]
    nlinarith only [hh, h130]
  have hbudget : (m : ℝ) * Real.log P ≤ P := by
    have hh := mul_le_mul_of_nonneg_right hmhi hlogP.le
    have hid : (A / Real.log P + 1) * Real.log P = A + Real.log P := by field_simp
    rw [hid] at hh
    linarith only [hh, hAhalf, log_le_half P hp0]
  have hpower : N ^ (65 * D ^ 3) ≤ P ^ m := by
    have hh : Real.log ((N : ℝ) ^ (65 * D ^ 3)) ≤ Real.log ((P : ℝ) ^ m) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast
      dsimp only [A] at hmlo
      nlinarith only [hmlo]
    have hi := (Real.log_le_log_iff (pow_pos hn0 _) (pow_pos hp0 _)).mp hh
    exact_mod_cast hi
  have hstrict : N ^ (64 * D ^ 3) < P ^ m := by
    have he : 64 * D ^ 3 < 65 * D ^ 3 := by
      have hdpos : 0 < D ^ 3 := by positivity
      omega
    exact (pow_lt_pow_right₀ (by omega : 1 < N) he).trans_le hpower
  have hDR : (D : ℝ) * R ≤ T := by
    have hh : (D : ℝ) ≤ (D : ℝ) ^ 3 * L :=
      (le_self_pow₀ hd (by decide : 3 ≠ 0)).trans (le_mul_of_one_le_right (by positivity) hL)
    exact mul_le_mul_of_nonneg_right hh (by positivity)
  have hroot : 3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤ P := by
    have hh := mul_le_mul_of_nonneg_left (DegreeUniformPrimeScale.box_root_bound D N hD)
      (by positivity : (0 : ℝ) ≤ 3 * Real.exp 1)
    have he : 6 * Real.exp 1 ≤ M := by linarith only [Real.exp_one_lt_three, hM]
    calc
      _ ≤ (6 * Real.exp 1) * ((D : ℝ) * R) := by convert hh using 1; ring
      _ ≤ M * T := mul_le_mul he hDR (by positivity) hM0.le
      _ ≤ _ := hceil
  have hupper : (P : ℝ) ≤ (M + 1) * T := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ M * T)).le
    change (P : ℝ) ≤ M * T + 1 at hh
    nlinarith only [hh, hT1]
  refine ⟨P, m, hP0, hm, hbudget, hstrict, hroot, hMC.trans hMPbound, ?_⟩
  simpa only [T, mul_assoc] using hupper

end PaperP1.EfficientDegreePrimeScale
