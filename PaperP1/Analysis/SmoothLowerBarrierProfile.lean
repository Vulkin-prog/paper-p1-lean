module

public import PaperP1.Analysis.ExponentialIntegral

/-! # A logarithmic barrier profile for a smooth-count lower induction

Only the analytic profile is proved here. The actual smooth counts and
prime-weight margins are supplied in separate arithmetic arguments.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothLowerBarrierProfile

open Set Filter

def cost (ε t : ℝ) : ℝ := t * (Real.log t + Real.log (Real.log t) - 1 + ε)

def tilt (ε t : ℝ) : ℝ := Real.log t + Real.log (Real.log t) + ε

def density (ε T t : ℝ) : ℝ := Real.exp (-cost ε (max T t))

theorem hasDerivAt_cost (ε t : ℝ) (ht : 1 < t) :
    HasDerivAt (cost ε) (tilt ε t + 1 / Real.log t) t := by
  have ht0 : 0 < t := by linarith only [ht]
  have hlog := Real.log_pos ht
  have h₁ := Real.hasDerivAt_log ht0.ne'
  have h₂ := (Real.hasDerivAt_log hlog.ne').comp t h₁
  have hh := (hasDerivAt_id t).mul (((h₁.add h₂).sub_const 1).add_const ε)
  apply hh.congr_deriv
  simp only [tilt, Pi.add_apply, Function.comp_apply, id_eq]
  field_simp
  ring

theorem tilt_monotone (ε : ℝ) : MonotoneOn (tilt ε) (Ioi 1) := by
  intro x hx y _hy hxy
  have hx0 : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx
  have hl := Real.log_le_log hx0 hxy
  have hll := Real.log_le_log (Real.log_pos hx) hl
  dsimp only [tilt]
  linarith only [hl, hll]

theorem tilt_nonneg (ε t : ℝ) (hε : 0 ≤ ε) (ht : Real.exp 1 ≤ t) : 0 ≤ tilt ε t := by
  have ht0 := (Real.exp_pos 1).trans_le ht
  have hl := Real.log_le_log (Real.exp_pos 1) ht
  rw [Real.log_exp] at hl
  have hll := Real.log_nonneg hl
  dsimp only [tilt]
  linarith only [hl, hll, hε]

theorem cost_nonneg (ε t : ℝ) (hε : 0 ≤ ε) (ht : Real.exp 1 ≤ t) : 0 ≤ cost ε t := by
  have ht0 := (Real.exp_pos 1).trans_le ht
  have hl := Real.log_le_log (Real.exp_pos 1) ht
  rw [Real.log_exp] at hl
  have hll := Real.log_nonneg hl
  dsimp only [cost]
  exact mul_nonneg ht0.le (by linarith only [hl, hll, hε])

theorem cost_monotone (ε : ℝ) (hε : 0 ≤ ε) : MonotoneOn (cost ε) (Ici (Real.exp 1)) := by
  have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hd (x : ℝ) (hx : x ∈ Ici (Real.exp 1)) :
      HasDerivAt (cost ε) (tilt ε x + 1 / Real.log x) x :=
    hasDerivAt_cost ε x (he.trans_le hx)
  apply monotoneOn_of_deriv_nonneg (convex_Ici (Real.exp 1))
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(hd x (interior_subset hx)).deriv]
  exact add_nonneg (tilt_nonneg ε x hε (interior_subset hx))
    (one_div_nonneg.mpr (Real.log_pos (he.trans_le (interior_subset hx))).le)

theorem cost_shift (ε t s : ℝ) (ht : 2 < t) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s * tilt ε (t - 1) ≤ cost ε t - cost ε (t - s) := by
  have hbase : 1 < t - 1 := by linarith only [ht]
  have hd (x : ℝ) (hx : x ∈ Ici (t - 1)) :
      HasDerivAt (cost ε) (tilt ε x + 1 / Real.log x) x :=
    hasDerivAt_cost ε x (hbase.trans_le hx)
  have hderiv (x : ℝ) (hx : x ∈ interior (Ici (t - 1))) : tilt ε (t - 1) ≤ deriv (cost ε) x := by
    have hx' : t - 1 ≤ x := interior_subset hx
    rw [(hd x hx').deriv]
    exact (tilt_monotone ε hbase (hbase.trans_le hx') hx').trans
      (le_add_of_nonneg_right (one_div_nonneg.mpr (Real.log_pos (hbase.trans_le hx')).le))
  have hh := (convex_Ici (t - 1)).mul_sub_le_image_sub_of_le_deriv
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    hderiv (t - s) (by change t - 1 ≤ t - s; linarith only [hs1]) t
      (by change t - 1 ≤ t; linarith) (by linarith only [hs] : t - s ≤ t)
  have hid : t - (t - s) = s := by ring
  simpa only [hid, mul_comm] using hh

theorem density_pos (ε T t : ℝ) : 0 < density ε T t := Real.exp_pos _

theorem density_le_one (ε T t : ℝ) (hε : 0 ≤ ε) (hT : Real.exp 1 ≤ T) : density ε T t ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (cost_nonneg ε _ hε (hT.trans (le_max_left _ _))))

theorem density_antitone (ε T : ℝ) (hε : 0 ≤ ε) (hT : Real.exp 1 ≤ T) : Antitone (density ε T) := by
  intro x y hxy
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (cost_monotone ε hε (hT.trans (le_max_left _ _))
    (hT.trans (le_max_left _ _)) (max_le_max le_rfl hxy))

theorem density_shift (ε T t s : ℝ) (hT : Real.exp 1 ≤ T) (ht : T + 1 ≤ t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    density ε T t * Real.exp (s * tilt ε (t - 1)) ≤ density ε T (t - s) := by
  have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have ht2 : 2 < t := by linarith only [he, hT, ht]
  have hTt : T ≤ t := by linarith only [ht]
  have hTts : T ≤ t - s := by linarith only [ht, hs1]
  rw [density, density, max_eq_right hTt, max_eq_right hTts, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := cost_shift ε t s ht2 hs hs1
  linarith only [hh]

end PaperP1.SmoothLowerBarrierProfile
