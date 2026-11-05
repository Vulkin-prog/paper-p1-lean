module

public import PaperP1.Algebra.PolynomialAuxiliaryExceptions
public import PaperP1.Analysis.PolynomialVelocitySmooth
public import Mathlib.Topology.Instances.Sign

/-! # Actual polynomial quotient signs off the auxiliary exceptional locus -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialQuotientControl

open MvPolynomial Set PolynomialVelocitySmooth

variable {X ι : Type*} [TopologicalSpace X]

theorem quotient_continuous (N A : MvPolynomial (Fin 2) ℝ) (e : ℕ)
    (s : Set X) (ζ : X → Fin 2 → ℝ) (hζ : ContinuousOn ζ s)
    (hA : ∀ t ∈ s, eval (ζ t) A ≠ 0) :
    ContinuousOn (fun t ↦ eval (ζ t) N / (eval (ζ t) A) ^ e) s := by
  have hN : ContinuousOn (fun t ↦ eval (ζ t) N) s :=
    (contDiff_eval N 1).continuous.comp_continuousOn hζ
  have hAc : ContinuousOn (fun t ↦ eval (ζ t) A) s :=
    (contDiff_eval A 1).continuous.comp_continuousOn hζ
  exact hN.div (hAc.pow e) (fun t ht ↦ pow_ne_zero e (hA t ht))

omit [TopologicalSpace X] in
theorem zero_or_nowhere_zero (P : MvPolynomial (Fin 2) ℝ)
    (f : ι → MvPolynomial (Fin 2) ℝ) (A : MvPolynomial (Fin 2) ℝ) (e : ℕ)
    (s : Set X) (ζ : X → Fin 2 → ℝ)
    (hcurve : ∀ t ∈ s, eval (ζ t) P = 0 ∧ ζ t ∉ PolynomialAuxiliaryExceptions.points P f)
    (hA : ∀ t ∈ s, eval (ζ t) A ≠ 0) (i : ι) :
    (∀ t ∈ s, eval (ζ t) (f i) / (eval (ζ t) A) ^ e = 0) ∨
    (∀ t ∈ s, eval (ζ t) (f i) / (eval (ζ t) A) ^ e ≠ 0) := by
  by_cases hdiv : P ∣ f i
  · apply Or.inl
    intro t ht
    rw [PolynomialAuxiliaryExceptions.zero_of_divisible P (f i) (ζ t) (hcurve t ht).1 hdiv, zero_div]
  · apply Or.inr
    intro t ht
    have hn := (PolynomialAuxiliaryExceptions.divisible_or_nonzero P f (ζ t)
      (hcurve t ht).1 (hcurve t ht).2 i).resolve_left hdiv
    exact div_ne_zero hn (pow_ne_zero e (hA t ht))

theorem sign_constant (P : MvPolynomial (Fin 2) ℝ)
    (f : ι → MvPolynomial (Fin 2) ℝ) (A : MvPolynomial (Fin 2) ℝ) (e : ℕ)
    (s : Set X) (hs : IsPreconnected s) (ζ : X → Fin 2 → ℝ) (hζ : ContinuousOn ζ s)
    (hcurve : ∀ t ∈ s, eval (ζ t) P = 0 ∧ ζ t ∉ PolynomialAuxiliaryExceptions.points P f)
    (hA : ∀ t ∈ s, eval (ζ t) A ≠ 0) (i : ι) (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (eval (ζ x) (f i) / (eval (ζ x) A) ^ e) =
      SignType.sign (eval (ζ y) (f i) / (eval (ζ y) A) ^ e) := by
  rcases zero_or_nowhere_zero P f A e s ζ hcurve hA i with hz | hn
  · rw [hz x hx, hz y hy]
  · exact hs.sign_eq_of_continuousOn (quotient_continuous (f i) A e s ζ hζ hA) hn hx hy

end PaperP1.PolynomialQuotientControl
