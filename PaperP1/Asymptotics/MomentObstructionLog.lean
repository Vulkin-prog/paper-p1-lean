module

public import PaperP1.Asymptotics.FactorialLogBounds
public import PaperP1.Probability.MomentObstruction

/-! # A finite logarithmic error bound for the moment-obstruction distance

The floor and the factorial error are retained explicitly. This supplies
the unnumbered asymptotic following T23.1 without assuming Stirling's formula.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MomentObstructionLog

open PaperP1.MomentObstructionMass PaperP1.MomentObstruction PaperP1.FactorialLogBounds

def distance (m : ℕ) (a : ℝ) : ℝ :=
  (1 - a / 2) * (2 : ℝ) ^ (m - 2) / (Real.exp 1 * (m.factorial : ℝ))

theorem distance_eq_totalVariation (m : ℕ) (hm : 3 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    distance m a = AtomicProbability.totalVariation
      (pLaw m (by omega) a ha0 (by linarith)) (qLaw a ha0 (by linarith)) :=
  (totalVariation_exact m (by omega) (by omega) a ha0 (by linarith)).symm

theorem distance_pos (m : ℕ) (a : ℝ) (ha1 : a ≤ 1) : 0 < distance m a := by
  unfold distance
  have h : 0 < 1 - a / 2 := by linarith
  positivity

theorem log_distance_formula (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha1 : a ≤ 1) :
    Real.log (distance m a) = Real.log (1 - a / 2) + ((m : ℝ) - 2) * Real.log 2 - 1 -
      Real.log (m.factorial : ℝ) := by
  have ha : 0 < 1 - a / 2 := by linarith
  unfold distance
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul ha.ne' (by positivity),
    Real.log_pow, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Nat.cast_sub hm]
  norm_num
  ring

theorem log_distance_error (m : ℕ) (hm : 3 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |Real.log (distance m a) + (m : ℝ) * Real.log m| ≤ 2 * (m : ℝ) := by
  rw [log_distance_formula m (by omega) a ha1]
  have hfac := log_factorial_bounds m (by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl2one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have ha : 0 < 1 - a / 2 := by linarith
  have halower : -Real.log 2 ≤ Real.log (1 - a / 2) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤ 1 - a / 2 by linarith)
    norm_num [Real.log_div] at h
    exact h
  have haupper : Real.log (1 - a / 2) ≤ 0 :=
    Real.log_nonpos ha.le (by linarith)
  have hp0 : 0 ≤ ((m : ℝ) - 2) * Real.log 2 := mul_nonneg (by linarith) hl2
  have hp1 : ((m : ℝ) - 2) * Real.log 2 ≤ (m : ℝ) - 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hl2one (show 0 ≤ (m : ℝ) - 2 by linarith)
  apply abs_le.mpr
  constructor <;> linarith

theorem floor_mul_log_error (x : ℝ) (hx : 3 ≤ x) :
    |(⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - x * Real.log x| ≤ x := by
  have hxpos : 0 < x := by linarith
  have hm : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hmpos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hxm : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have hlogm : 0 ≤ Real.log (⌊x⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogs : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log hmpos hmx
  have hprod : (⌊x⌋₊ : ℝ) * (Real.log x - Real.log (⌊x⌋₊ : ℝ)) ≤ x - (⌊x⌋₊ : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos hxpos hmpos)
    rw [Real.log_div hxpos.ne' hmpos.ne'] at h
    have h' := mul_le_mul_of_nonneg_left h hmpos.le
    have heq : (⌊x⌋₊ : ℝ) * (x / (⌊x⌋₊ : ℝ) - 1) = x - (⌊x⌋₊ : ℝ) := by
      field_simp
    rwa [heq] at h'
  have hsmall : (x - (⌊x⌋₊ : ℝ)) * Real.log x ≤ Real.log x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show x - (⌊x⌋₊ : ℝ) ≤ 1 by linarith) hlogx
  have hmono : (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) ≤ x * Real.log x :=
    mul_le_mul hmx hlogs hlogm hxpos.le
  have hlogbound := Real.log_le_sub_one_of_pos hxpos
  apply abs_le.mpr
  constructor <;> nlinarith

theorem log_distance_floor_error (x : ℝ) (hx : 3 ≤ x) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |Real.log (distance ⌊x⌋₊ a) + x * Real.log x| ≤ 3 * x := by
  have hm : 3 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  calc
    _ = |(Real.log (distance ⌊x⌋₊ a) + (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ)) -
        ((⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - x * Real.log x)| := by congr 1; ring
    _ ≤ |Real.log (distance ⌊x⌋₊ a) + (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ)| +
        |(⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - x * Real.log x| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (Real.log (distance ⌊x⌋₊ a) + (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ)) 0
          ((⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) - x * Real.log x)
    _ ≤ 2 * (⌊x⌋₊ : ℝ) + x :=
      add_le_add (log_distance_error _ hm a ha0 ha1) (floor_mul_log_error x hx)
    _ ≤ _ := by linarith

theorem log_distance_sqrt_log_bound (N : ℕ) (hN : 9 ≤ Real.log N) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |Real.log (distance ⌊Real.sqrt (Real.log N)⌋₊ a) +
        (1 / 2) * Real.sqrt (Real.log N) * Real.log (Real.log N)| ≤
      3 * Real.sqrt (Real.log N) := by
  have hlog : 0 ≤ Real.log N := by linarith
  have hx : 3 ≤ Real.sqrt (Real.log N) := (Real.le_sqrt (by norm_num) hlog).mpr (by nlinarith)
  have h := log_distance_floor_error (Real.sqrt (Real.log N)) hx a ha0 ha1
  rw [Real.log_sqrt hlog] at h
  convert h using 1
  congr 1
  ring

end PaperP1.MomentObstructionLog
