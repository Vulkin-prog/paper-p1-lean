module

public import PaperP1.Arithmetic.ShortBasisTheorem
public import PaperP1.Analysis.CurveDegreeAsymptotics
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # All numerical power and logarithmic budgets between a short basis and its actual curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisCurveScale

open Filter PaperP1.CurveDegreeAsymptotics

def extractionExponent (ε : ℝ) : ℝ := Real.exp (-(3 * ε / 8)) / 2

theorem extractionExponent_choice (ε : ℝ) (hε : 0 < ε) :
    0 < extractionExponent ε ∧ extractionExponent ε < 1 / 2 ∧
      (2 / 3) * Real.log (1 / extractionExponent ε) = (2 / 3) * Real.log 2 + ε / 4 := by
  have he := Real.exp_pos (-(3 * ε / 8))
  have hsmall : Real.exp (-(3 * ε / 8)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have ha : 0 < extractionExponent ε := by unfold extractionExponent; positivity
  refine ⟨ha, by unfold extractionExponent; linarith, ?_⟩
  rw [Real.log_div one_ne_zero ha.ne', Real.log_one]
  unfold extractionExponent
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp]
  ring

def halfBudget (b : ℝ) (B : ℕ) : ℕ := ⌊(B : ℝ) ^ b⌋₊

theorem support_budget_eventually (a b K : ℝ) (hab : a < b) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hK : 0 < K) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      1 ≤ halfBudget b B ∧ halfBudget b B ≤ B ∧
      K * (B : ℝ) ^ a * Real.log B / Real.log (Real.log B) ≤ (2 * halfBudget b B : ℕ) := by
  have hgap : 0 < b - a := by linarith
  have hs := (((PNT.tendsto_pow_log_div_pow_atTop (b - a) 1 hgap).const_mul K).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (show K * (0 : ℝ) < 1 by simp))
  have hl := (Real.tendsto_log_atTop.comp PrimeLogBudget.log_nat_tendsto_atTop).eventually
    (eventually_ge_atTop 1)
  have hp := ((tendsto_rpow_atTop hb).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop 2)
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp (hs.and (hl.and hp))
  refine ⟨max B₁ 2, by omega, ?_⟩
  intro B hB
  obtain ⟨hsB, hlB, hpB⟩ := hB₁ B (by omega)
  dsimp only [Function.comp_def] at hlB hpB
  have hBtwo : 2 ≤ B := by omega
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hs₀ : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBone
  have hpow : 0 < (B : ℝ) ^ (b - a) := Real.rpow_pos_of_pos hBp _
  have hsmall : K * Real.log B / (B : ℝ) ^ (b - a) ≤ 1 := by
    simpa only [Function.comp_def, Real.rpow_one, div_eq_mul_inv, mul_assoc] using hsB.le
  have hnum := (div_le_iff₀ hpow).mp hsmall
  have hscaled : K * (B : ℝ) ^ a * Real.log B ≤ (B : ℝ) ^ b := by
    calc
      K * (B : ℝ) ^ a * Real.log B = (B : ℝ) ^ a * (K * Real.log B) := by ring
      _ ≤ (B : ℝ) ^ a * (B : ℝ) ^ (b - a) := mul_le_mul_of_nonneg_left (by simpa using hnum) (by positivity)
      _ = (B : ℝ) ^ b := by rw [← Real.rpow_add hBp]; congr 1; ring
  have hqone : 1 ≤ halfBudget b B := by
    apply Nat.le_floor
    norm_num
    linarith
  have hqle : halfBudget b B ≤ B := by
    have hfloor := Nat.floor_le (Real.rpow_nonneg hBp.le b)
    have hself := Real.rpow_le_self_of_one_le hBone hb₁
    exact_mod_cast hfloor.trans hself
  have hdouble : (B : ℝ) ^ b ≤ ((2 * halfBudget b B : ℕ) : ℝ) := by
    have hfloor := Nat.lt_floor_add_one ((B : ℝ) ^ b)
    dsimp [halfBudget]
    push_cast
    linarith
  refine ⟨hqone, hqle, ?_⟩
  exact (div_le_self (by positivity) hlB).trans (hscaled.trans hdouble)

theorem log_succ_le (B : ℕ) (hB : 2 ≤ B) : Real.log ((B : ℝ) + 1) ≤ 2 * Real.log B := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have htwo : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hmono := Real.log_le_log (by linarith : 0 < (B : ℝ) + 1)
    (show (B : ℝ) + 1 ≤ 2 * B by linarith)
  rw [Real.log_mul (by norm_num) hBp.ne'] at hmono
  have hlogtwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) htwo
  linarith

theorem logarithmic_budget_eventually (b η : ℝ) (hb : b < 1 / 2) (hη : 0 < η) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      (B : ℝ) ^ (2 * b) * Real.log ((B : ℝ) + 1) ≤ η * B := by
  have hs := ((PNT.tendsto_pow_log_div_pow_atTop (1 - 2 * b) 1 (by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (div_pos hη (show (0 : ℝ) < 2 by norm_num)))
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp hs
  refine ⟨max B₁ 2, by omega, ?_⟩
  intro B hB
  have hBtwo : 2 ≤ B := by omega
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hp : 0 < (B : ℝ) ^ (1 - 2 * b) := Real.rpow_pos_of_pos hBp _
  have hsmall : Real.log B / (B : ℝ) ^ (1 - 2 * b) ≤ η / 2 := by
    simpa only [Function.comp_def, Real.rpow_one] using (hB₁ B (by omega)).le
  have hm := (div_le_iff₀ hp).mp hsmall
  have hprod := mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * (B : ℝ) ^ (2 * b) by positivity)
  have hpower : (B : ℝ) ^ (2 * b) * (B : ℝ) ^ (1 - 2 * b) = B := by
    rw [← Real.rpow_add hBp]
    norm_num
  have hlog := mul_le_mul_of_nonneg_left (log_succ_le B hBtwo)
    (Real.rpow_nonneg hBp.le (2 * b))
  calc
    (B : ℝ) ^ (2 * b) * Real.log ((B : ℝ) + 1) ≤ η *
        ((B : ℝ) ^ (2 * b) * (B : ℝ) ^ (1 - 2 * b)) := by nlinarith
    _ = η * B := by rw [hpower]

theorem dimension_budget_eventually (b η : ℝ) (hb : b < 1 / 2) (hη : 0 < η) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, 1 + 13824 * (B : ℝ) ^ (2 * b) ≤ η * B := by
  have hi := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hp := (PNT.tendsto_pow_log_div_pow_atTop (1 - 2 * b) 0 (by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlim : Tendsto (fun B : ℕ ↦ (B : ℝ)⁻¹ + 13824 * (1 / (B : ℝ) ^ (1 - 2 * b)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_zero, mul_zero, add_zero] using hi.add (hp.const_mul 13824)
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hη))
  refine ⟨max B₁ 2, by omega, ?_⟩
  intro B hB
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have heq : (1 + 13824 * (B : ℝ) ^ (2 * b)) / B =
      (B : ℝ)⁻¹ + 13824 * (1 / (B : ℝ) ^ (1 - 2 * b)) := by
    rw [add_div, mul_div_assoc, power_div_scale (B : ℝ) (2 * b) hBp]
    ring
  apply (div_le_iff₀ hBp).mp
  rw [heq]
  exact (hB₁ B (by omega)).le

theorem extraction_error_eventually (K η : ℝ) (hη : 0 < η) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, K / Real.sqrt (Real.log B) ≤ η := by
  have hr : Tendsto (fun B : ℕ ↦ Real.sqrt (Real.log B)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp PrimeLogBudget.log_nat_tendsto_atTop
  have hi := tendsto_inv_atTop_zero.comp hr
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp
    ((hi.const_mul K).eventually (eventually_lt_nhds (by simpa only [mul_zero] using hη)))
  refine ⟨max B₁ 2, by omega, ?_⟩
  intro B hB
  simpa only [div_eq_mul_inv, Function.comp_def] using (hB₁ B (by omega)).le

theorem rank_threshold_eventually (η : ℝ) (hη : 0 < η) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, 9 ≤ η * B := by
  obtain ⟨B₁, hB₁⟩ := exists_nat_gt (9 / η)
  refine ⟨max B₁ 2, by omega, ?_⟩
  intro B hB
  have hs : 9 / η < (B : ℝ) := hB₁.trans_le (by exact_mod_cast (show B₁ ≤ B by omega))
  have hm := (div_lt_iff₀ hη).mp hs
  linarith

theorem point_threshold_of_log_budget (B q : ℕ) (N U : ℝ) (hB : 2 ≤ B) (hN : 1 < N)
    (hU : 0 < U) (hscale : (B : ℝ) ≤ U * Real.log N)
    (hbudget : 1000000 * (q : ℝ) ^ 2 * Real.log ((B : ℝ) + 1) ≤ (B : ℝ) / (2 * U)) :
    ((B : ℝ) + 1) ^ (1000000 * q ^ 2) < N := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hhalf : (B : ℝ) / (2 * U) ≤ Real.log N / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hU)).mpr
    nlinarith
  apply (Real.log_lt_log_iff (pow_pos (by linarith : 0 < (B : ℝ) + 1) _) (by linarith : 0 < N)).mp
  rw [Real.log_pow]
  have heq : ((1000000 * q ^ 2 : ℕ) : ℝ) = 1000000 * (q : ℝ) ^ 2 := by norm_num
  rw [heq]
  linarith

theorem point_threshold_eventually (b U : ℝ) (hb : b < 1 / 2) (hU : 0 < U) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ q : ℕ, (q : ℝ) ≤ (B : ℝ) ^ b →
      ∀ N : ℝ, 1 < N → (B : ℝ) ≤ U * Real.log N →
        ((B : ℝ) + 1) ^ (1000000 * q ^ 2) < N := by
  let η : ℝ := 1 / (2000000 * U)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨B₀, hB₀, hbudget⟩ := logarithmic_budget_eventually b η hb hη
  refine ⟨B₀, hB₀, ?_⟩
  intro B hB q hq N hN hscale
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hqpow : (q : ℝ) ^ 2 ≤ (B : ℝ) ^ (2 * b) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) q) hq 2
    rw [← Real.rpow_mul_natCast hBp.le b 2] at h
    convert h using 1
    congr 1
    ring
  have hlog : 0 ≤ Real.log ((B : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hprod := mul_le_mul_of_nonneg_right hqpow hlog
  apply point_threshold_of_log_budget B q N U (by omega) hN hU hscale
  calc
    1000000 * (q : ℝ) ^ 2 * Real.log ((B : ℝ) + 1) ≤ 1000000 * (η * B) := by
      have hbB := hbudget B hB
      nlinarith
    _ = (B : ℝ) / (2 * U) := by dsimp [η]; field_simp; norm_num

theorem degree_loss_of_power_bound (B b : ℝ) (D : ℕ) (hB : 0 < B)
    (hD : (D : ℝ) ≤ 48 * B ^ b) :
    1 + 6 * (D : ℝ) ^ 2 ≤ 1 + 13824 * B ^ (2 * b) := by
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) D) hD 2
  have hp : (B ^ b) ^ 2 = B ^ (2 * b) := by
    rw [← Real.rpow_mul_natCast hB.le b 2]
    congr 1
    ring
  rw [mul_pow, hp] at hs
  norm_num at hs
  nlinarith

theorem rank_threshold_lt_half : (2 / 3 : ℝ) * Real.log 2 < 1 / 2 := by
  have hp : (2 : ℝ) < (35 / 32 : ℝ) ^ 8 := by norm_num
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) hp
  rw [Real.log_pow] at hl
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 35 / 32 by norm_num)
  norm_num at hl hlog
  linarith

end PaperP1.ShortBasisCurveScale
