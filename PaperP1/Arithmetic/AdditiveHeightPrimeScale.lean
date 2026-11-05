module

public import PaperP1.Arithmetic.EfficientDegreePrimeScale

/-! # An additive prime scale for a variable height obstruction

The logarithmic height allowance and the determinant root are added.
The absolute constant precedes every obstruction exponent and root degree.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AdditiveHeightPrimeScale

open DegreeUniformAffineParameters

theorem exists_scale (P₀ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ E N b : ℕ, 2 ≤ N →
      ∃ P m : ℕ, P₀ ≤ P ∧ 1 ≤ m ∧ (m : ℝ) * Real.log P ≤ P ∧ N ^ E < P ^ m ∧
        3 * Real.exp 1 * (N : ℝ) ^ (1 / (b : ℝ)) ≤ P ∧ 3 * Real.exp 4 ≤ P ∧
        (P : ℝ) ≤ K * ((((E + 1 : ℕ) : ℝ) * logarithmicBudget N) + (N : ℝ) ^ (1 / (b : ℝ))) := by
  let M : ℝ := P₀ + (⌈3 * Real.exp 4⌉₊ : ℝ) + 8192
  have hM : 8192 ≤ M := by
    have hp := Nat.cast_nonneg (α := ℝ) P₀
    have hc := Nat.cast_nonneg (α := ℝ) ⌈3 * Real.exp 4⌉₊
    dsimp only [M]
    linarith only [hp, hc]
  have hM0 : 0 < M := by linarith only [hM]
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
  intro E N b hN
  let L := logarithmicBudget N
  let R := (N : ℝ) ^ (1 / (b : ℝ))
  let T := ((E + 1 : ℕ) : ℝ) * L + R
  let P := ⌈M * T⌉₊
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hn0 : (0 : ℝ) < N := by linarith only [hn]
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hE : (1 : ℝ) ≤ ((E + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ E + 1 by omega)
  have hR : 1 ≤ R := Real.one_le_rpow hn.le (by positivity)
  have hT1 : 1 ≤ T := by
    have hh : (1 : ℝ) ≤ ((E + 1 : ℕ) : ℝ) * L := by nlinarith only [hE, hL, mul_nonneg (sub_nonneg.mpr hE) (sub_nonneg.mpr hL)]
    dsimp only [T]
    linarith only [hh, hR]
  have hceil : M * T ≤ (P : ℝ) := Nat.le_ceil _
  have hMPbound : M ≤ (P : ℝ) := (le_mul_of_one_le_right hM0.le hT1).trans hceil
  have hP0 : P₀ ≤ P := by exact_mod_cast hMP.trans hMPbound
  have hp1 : (1 : ℝ) < P := by linarith only [hMPbound, hM]
  have hp0 : (0 : ℝ) < P := by linarith only [hp1]
  have hlogP : 0 < Real.log P := Real.log_pos hp1
  have hlogN : 0 < Real.log N := Real.log_pos hn
  let A := ((E + 1 : ℕ) : ℝ) * Real.log N
  let m := ⌈A / Real.log P⌉₊
  have hA : 0 < A := by dsimp only [A]; positivity
  have hm : 1 ≤ m := Nat.one_le_ceil_iff.mpr (by positivity)
  have hmhi : (m : ℝ) ≤ A / Real.log P + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmlo : A ≤ (m : ℝ) * Real.log P := (div_le_iff₀ hlogP).mp (Nat.le_ceil (A / Real.log P))
  have hlogBudget : Real.log N ≤ (L : ℝ) := log_le_budget N (by omega)
  have hAT : A ≤ T := by
    have hh := mul_le_mul_of_nonneg_left hlogBudget (by positivity : (0 : ℝ) ≤ ((E + 1 : ℕ) : ℝ))
    dsimp only [A, T]
    linarith only [hh, hR]
  have hAhalf : A ≤ (P : ℝ) / 2 := by
    have hh := mul_le_mul_of_nonneg_right (by linarith only [hM] : (2 : ℝ) ≤ M) (by linarith only [hT1] : 0 ≤ T)
    nlinarith only [hAT, hh, hceil]
  have hbudget : (m : ℝ) * Real.log P ≤ P := by
    have hh := mul_le_mul_of_nonneg_right hmhi hlogP.le
    have hid : (A / Real.log P + 1) * Real.log P = A + Real.log P := by field_simp
    rw [hid] at hh
    linarith only [hh, hAhalf, EfficientDegreePrimeScale.log_le_half P hp0]
  have hpower : N ^ (E + 1) ≤ P ^ m := by
    have hh : Real.log ((N : ℝ) ^ (E + 1)) ≤ Real.log ((P : ℝ) ^ m) := by
      rw [Real.log_pow, Real.log_pow]
      dsimp only [A] at hmlo
      nlinarith only [hmlo]
    have hi := (Real.log_le_log_iff (pow_pos hn0 _) (pow_pos hp0 _)).mp hh
    exact_mod_cast hi
  have hstrict : N ^ E < P ^ m :=
    (pow_lt_pow_right₀ (by omega : 1 < N) (Nat.lt_succ_self E)).trans_le hpower
  have hRT : R ≤ T := by dsimp only [T]; exact le_add_of_nonneg_left (by positivity)
  have hroot : 3 * Real.exp 1 * (N : ℝ) ^ (1 / (b : ℝ)) ≤ P := by
    have he : 3 * Real.exp 1 ≤ M := by linarith only [Real.exp_one_lt_three, hM]
    exact (mul_le_mul he hRT (by positivity) hM0.le).trans hceil
  have hupper : (P : ℝ) ≤ (M + 1) * T := by
    have hh := (Nat.ceil_lt_add_one (by positivity : 0 ≤ M * T)).le
    change (P : ℝ) ≤ M * T + 1 at hh
    nlinarith only [hh, hT1]
  exact ⟨P, m, hP0, hm, hbudget, hstrict, hroot, hMC.trans hMPbound, hupper⟩

end PaperP1.AdditiveHeightPrimeScale
