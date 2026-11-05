module

public import PaperP1.Analysis.PolynomialEvaluationDerivative
public import PaperP1.Analysis.PolynomialVelocitySmooth
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Actual local uniqueness of vertical polynomial roots at a regular point

The argument uses the actual derivative, Rolle's theorem and continuity of the
actual polynomial partial. No implicit-function or graph-uniqueness premise is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialVerticalRootUniqueness

open MvPolynomial Set Filter
open scoped Topology ContDiff


theorem point_eta (z : Fin 2 → ℝ) : ![z 0, z 1] = z := by
  funext i
  fin_cases i <;> rfl

theorem hasDerivAt_vertical (P : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    HasDerivAt (fun v : ℝ ↦ eval ![x, v] P) (eval ![x, y] (pderiv 1 P)) y := by
  have hf : ∀ i : Fin 2, HasDerivAt (fun v : ℝ ↦ ![x, v] i) (![(0 : ℝ), 1] i) y := by
    intro i
    fin_cases i
    · simpa using (hasDerivAt_const y x : HasDerivAt (fun _ : ℝ ↦ x) 0 y)
    · simpa using (hasDerivAt_id' y : HasDerivAt (fun v : ℝ ↦ v) 1 y)
  have hh := PolynomialEvaluationDerivative.hasDerivAt_eval P (fun i v ↦ ![x, v] i) ![(0 : ℝ), 1] y hf
  simpa [PolynomialEvaluationDerivative.directional, Fin.sum_univ_two] using hh

theorem vertical_roots_eq (P : MvPolynomial (Fin 2) ℝ) (x a b u v : ℝ)
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b)
    (hpartial : ∀ y ∈ Ioo a b, eval ![x, y] (pderiv 1 P) ≠ 0)
    (hPu : eval ![x, u] P = 0) (hPv : eval ![x, v] P = 0) : u = v := by
  have hsmooth : ContDiff ℝ ∞ (fun y : ℝ ↦ ![x, y]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun _ : ℝ ↦ x)
      exact contDiff_const
    · change ContDiff ℝ ∞ (fun y : ℝ ↦ y)
      exact contDiff_id
  have hcontinuous : Continuous (fun y : ℝ ↦ eval ![x, y] P) :=
    ((PolynomialVelocitySmooth.contDiff_eval P ∞).comp hsmooth).continuous
  have bad : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s < t → eval ![x, s] P = eval ![x, t] P → False := by
    intro s hs t ht hst he
    obtain ⟨y, hy, hzero⟩ := exists_deriv_eq_zero hst hcontinuous.continuousOn he
    have hd := (hasDerivAt_vertical P x y).deriv
    exact hpartial y ⟨hs.1.trans hy.1, hy.2.trans ht.2⟩ (hd.symm.trans hzero)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact bad u hu v hv hlt (hPu.trans hPv.symm)
  · exact bad v hv u hu hgt (hPv.trans hPu.symm)

theorem exists_nonzero_box (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hpartial : eval z (pderiv 1 P) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin 2 → ℝ, (∀ i, |w i - z i| < ε) → eval w (pderiv 1 P) ≠ 0 := by
  have hc : ContinuousAt (fun w : Fin 2 → ℝ ↦ eval w (pderiv 1 P)) z :=
    (PolynomialVelocitySmooth.contDiff_eval (pderiv 1 P) 1).continuous.continuousAt
  have hmem : {w : Fin 2 → ℝ | eval w (pderiv 1 P) ≠ 0} ∈ 𝓝 z := hc.eventually_ne hpartial
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨ε, hε, ?_⟩
  intro w hw
  apply hsub
  apply (dist_pi_lt_iff hε).mpr
  intro i
  simpa only [Real.dist_eq] using hw i

theorem exists_local_vertical_unique (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ)
    (hpartial : eval z (pderiv 1 P) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x u v : ℝ, |x - z 0| < ε → |u - z 1| < ε → |v - z 1| < ε →
      eval ![x, u] P = 0 → eval ![x, v] P = 0 → u = v := by
  obtain ⟨ε, hε, hbox⟩ := exists_nonzero_box P z hpartial
  refine ⟨ε, hε, ?_⟩
  intro x u v hx hu hv hPu hPv
  have hU : u ∈ Ioo (z 1 - ε) (z 1 + ε) := by
    have hh := abs_lt.mp hu
    exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  have hV : v ∈ Ioo (z 1 - ε) (z 1 + ε) := by
    have hh := abs_lt.mp hv
    exact ⟨by linarith only [hh.1], by linarith only [hh.2]⟩
  apply vertical_roots_eq P x (z 1 - ε) (z 1 + ε) u v hU hV _ hPu hPv
  intro y hy
  apply hbox ![x, y]
  intro i
  fin_cases i
  · exact hx
  · change |y - z 1| < ε
    exact abs_lt.mpr ⟨by linarith only [hy.1], by linarith only [hy.2]⟩

end PaperP1.PolynomialVerticalRootUniqueness
