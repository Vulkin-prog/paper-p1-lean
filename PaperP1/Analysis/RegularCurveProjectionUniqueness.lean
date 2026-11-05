module

public import PaperP1.Analysis.PolynomialVerticalRootUniqueness
public import Mathlib.Topology.SeparatedMap

/-! # Actual local injectivity and uniqueness of lifts for the regular curve projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularCurveProjectionUniqueness

open MvPolynomial Set PolynomialVerticalRootUniqueness


abbrev RegularX (P : MvPolynomial (Fin 2) ℝ) :=
  {z : Fin 2 → ℝ // eval z P = 0 ∧ eval z (pderiv 1 P) ≠ 0}

def projection {P : MvPolynomial (Fin 2) ℝ} (z : RegularX P) : ℝ := z.val 0

theorem projection_locally_injective (P : MvPolynomial (Fin 2) ℝ) :
    IsLocallyInjective (projection (P := P)) := by
  intro z
  obtain ⟨ε, hε, hunique⟩ := exists_local_vertical_unique P z.val z.property.2
  let U : Set (RegularX P) := {w | dist w.val z.val < ε}
  refine ⟨U, ?_, ?_, ?_⟩
  · exact Metric.isOpen_ball.preimage continuous_subtype_val
  · change dist z.val z.val < ε
    simpa only [dist_self] using hε
  · intro w hw v hv he
    change dist w.val z.val < ε at hw
    change dist v.val z.val < ε at hv
    have hW := (dist_pi_lt_iff hε).mp hw
    have hV := (dist_pi_lt_iff hε).mp hv
    change w.val 0 = v.val 0 at he
    have hx : |w.val 0 - z.val 0| < ε := by simpa only [Real.dist_eq] using hW 0
    have hwY : |w.val 1 - z.val 1| < ε := by simpa only [Real.dist_eq] using hW 1
    have hvY : |v.val 1 - z.val 1| < ε := by simpa only [Real.dist_eq] using hV 1
    have hwP : eval ![w.val 0, w.val 1] P = 0 := by rw [point_eta]; exact w.property.1
    have hvP : eval ![w.val 0, v.val 1] P = 0 := by rw [he, point_eta]; exact v.property.1
    have hy := hunique (w.val 0) (w.val 1) (v.val 1) hx hwY hvY hwP hvP
    apply Subtype.ext
    funext i
    fin_cases i
    · exact he
    · exact hy

theorem projection_separated (P : MvPolynomial (Fin 2) ℝ) : IsSeparatedMap (projection (P := P)) :=
  T2Space.isSeparatedMap _

theorem unique_lifts {A : Type*} [TopologicalSpace A] (P : MvPolynomial (Fin 2) ℝ)
    (s : Set A) (hs : IsPreconnected s) (f g : A → RegularX P)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hproj : ∀ t ∈ s, projection (f t) = projection (g t))
    (t₀ : A) (ht₀ : t₀ ∈ s) (he : f t₀ = g t₀) : EqOn f g s :=
  (projection_separated P).eqOn_of_comp_eqOn (projection_locally_injective P) hs hf hg hproj ht₀ he

end PaperP1.RegularCurveProjectionUniqueness
