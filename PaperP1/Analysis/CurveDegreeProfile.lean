module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # The exact degree-uniform endpoint bound in the integer-point estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveDegreeProfile

open Set

def profile (H D : ℝ) : ℝ := D ^ 2 * H ^ (1 / D)

def logarithmic (H s : ℝ) : ℝ := 2 * s + Real.log H * Real.exp (-s)

theorem logarithmic_convex (H : ℝ) (hH : 1 ≤ H) : ConvexOn ℝ univ (logarithmic H) := by
  have he : ConvexOn ℝ univ (fun s : ℝ ↦ Real.exp (-s)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have h := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    convert h using 1
    simp only [smul_eq_mul]
    congr 1
    ring
  have hlin : ConvexOn ℝ univ (fun s : ℝ ↦ 2 * s) := by
    simpa only [smul_eq_mul, id_eq] using
      ConvexOn.smul (show (0 : ℝ) ≤ 2 by norm_num) (convexOn_id (convex_univ : Convex ℝ (univ : Set ℝ)))
  have hterm : ConvexOn ℝ univ (fun s : ℝ ↦ Real.log H * Real.exp (-s)) := by
    simpa only [smul_eq_mul] using ConvexOn.smul (Real.log_nonneg hH) he
  exact hlin.add hterm

theorem exp_logarithmic (H D : ℝ) (hH : 0 < H) (hD : 0 < D) :
    Real.exp (logarithmic H (Real.log D)) = profile H D := by
  unfold logarithmic profile
  rw [Real.exp_add, Real.exp_neg, Real.exp_log hD]
  have hp : Real.exp (2 * Real.log D) = D ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hD] using Real.exp_nat_mul (Real.log D) 2
  rw [hp, one_div, Real.rpow_def_of_pos hH]

theorem endpoint_bound (H D M : ℝ) (hH : 1 ≤ H) (hD : 2 ≤ D) (hDM : D ≤ M) :
    profile H D ≤ max (profile H 2) (profile H M) := by
  have hHp : 0 < H := by linarith
  have hDp : 0 < D := by linarith
  have hMp : 0 < M := by linarith
  have hd : Real.log D ∈ Icc (Real.log 2) (Real.log M) :=
    ⟨Real.log_le_log (by norm_num) hD, Real.log_le_log hDp hDM⟩
  have hm := (logarithmic_convex H hH).le_max_of_mem_Icc (mem_univ _) (mem_univ _) hd
  rcases le_total (logarithmic H (Real.log 2)) (logarithmic H (Real.log M)) with h | h
  · rw [max_eq_right h] at hm
    have he := Real.exp_le_exp.mpr hm
    rw [exp_logarithmic H D hHp hDp, exp_logarithmic H M hHp hMp] at he
    exact he.trans (le_max_right _ _)
  · rw [max_eq_left h] at hm
    have he := Real.exp_le_exp.mpr hm
    rw [exp_logarithmic H D hHp hDp, exp_logarithmic H 2 hHp (by norm_num)] at he
    exact he.trans (le_max_left _ _)

theorem large_endpoint (H M : ℝ) (hH : 0 < H) (hM : 0 < M) (hlog : Real.log H ≤ M) :
    profile H M ≤ Real.exp 1 * M ^ 2 := by
  have hratio : Real.log H * (1 / M) ≤ 1 := by
    simpa only [mul_one_div] using (div_le_iff₀ hM).mpr (by simpa using hlog)
  have he := Real.exp_le_exp.mpr hratio
  rw [← Real.rpow_def_of_pos hH] at he
  unfold profile
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg M)
  simpa only [mul_comm] using hm

theorem degree_uniform_bound (H D M : ℝ) (hH : 1 ≤ H) (hD : 2 ≤ D) (hDM : D ≤ M)
    (hlog : Real.log H ≤ M) :
    profile H D ≤ 4 * H ^ (1 / 2 : ℝ) + Real.exp 1 * M ^ 2 := by
  have hHp : 0 < H := by linarith
  have hMp : 0 < M := by linarith
  have he := endpoint_bound H D M hH hD hDM
  have hlarge := large_endpoint H M hHp hMp hlog
  have htwo : profile H 2 = 4 * H ^ (1 / 2 : ℝ) := by norm_num [profile]
  rw [htwo] at he
  exact he.trans (max_le
    (le_add_of_nonneg_right (by positivity))
    (hlarge.trans (le_add_of_nonneg_left (by positivity))))

theorem degree_uniform_bound_without_cap_growth (H D M : ℝ) (hH : 1 ≤ H)
    (hD : 2 ≤ D) (hDM : D ≤ M) :
    profile H D ≤ 4 * H ^ (1 / 2 : ℝ) + Real.exp 1 * (M ^ 2 + Real.log H ^ 2) := by
  by_cases hlog : Real.log H ≤ M
  · have h := degree_uniform_bound H D M hH hD hDM hlog
    have hp : 0 ≤ Real.exp 1 * Real.log H ^ 2 := by positivity
    nlinarith
  · have hM : M < Real.log H := by linarith
    have h := degree_uniform_bound H D (Real.log H) hH hD (hDM.trans hM.le) (le_refl _)
    have hp : 0 ≤ Real.exp 1 * M ^ 2 := by positivity
    nlinarith

end PaperP1.CurveDegreeProfile
