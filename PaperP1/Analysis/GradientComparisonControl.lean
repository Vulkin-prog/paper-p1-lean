module

public import PaperP1.Analysis.PolynomialQuotientControl
public import PaperP1.Algebra.GraphControlExceptions
public import Mathlib.Basic.Sign.Basic

/-! # A consistent smaller-slope orientation on a connected nonexceptional set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradientComparisonControl

open MvPolynomial Set GraphControlPolynomials

def balance (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) : ℝ :=
  (eval z (pderiv 0 P)) ^ 2 - (eval z (pderiv 1 P)) ^ 2

theorem balance_factorization (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    balance P z = eval z (static P 2) * eval z (static P 3) := by
  change (eval z (pderiv 0 P)) ^ 2 - (eval z (pderiv 1 P)) ^ 2 =
    eval z (pderiv 0 P + pderiv 1 P) * eval z (pderiv 0 P - pderiv 1 P)
  simp only [map_add, map_sub]
  ring

variable {X : Type*} [TopologicalSpace X]

theorem static_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (s : Set X)
    (hs : IsPreconnected s) (ζ : X → Fin 2 → ℝ) (hc : ContinuousOn ζ s)
    (hcurve : ∀ t ∈ s, eval (ζ t) P = 0 ∧ ζ t ∉ GraphControlExceptions.points P r)
    (i : Fin 10) (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (eval (ζ x) (static P i)) = SignType.sign (eval (ζ y) (static P i)) := by
  have hA : ∀ t ∈ s, eval (ζ t) (1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro t _ht
    simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]
  have hh := PolynomialQuotientControl.sign_constant P (family P r) 1 0 s hs ζ hc hcurve hA
    (Sum.inl i) x y hx hy
  simpa only [family, Sum.elim_inl, map_one, pow_zero, div_one] using hh

theorem balance_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (s : Set X)
    (hs : IsPreconnected s) (ζ : X → Fin 2 → ℝ) (hc : ContinuousOn ζ s)
    (hcurve : ∀ t ∈ s, eval (ζ t) P = 0 ∧ ζ t ∉ GraphControlExceptions.points P r)
    (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (balance P (ζ x)) = SignType.sign (balance P (ζ y)) := by
  rw [balance_factorization, balance_factorization, sign_mul, sign_mul,
    static_sign P r s hs ζ hc hcurve 2 x y hx hy,
    static_sign P r s hs ζ hc hcurve 3 x y hx hy]

theorem abs_le_propagates (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (s : Set X)
    (hs : IsPreconnected s) (ζ : X → Fin 2 → ℝ) (hc : ContinuousOn ζ s)
    (hcurve : ∀ t ∈ s, eval (ζ t) P = 0 ∧ ζ t ∉ GraphControlExceptions.points P r)
    (x₀ : X) (hx₀ : x₀ ∈ s)
    (hinit : |eval (ζ x₀) (pderiv 0 P)| ≤ |eval (ζ x₀) (pderiv 1 P)|)
    (x : X) (hx : x ∈ s) : |eval (ζ x) (pderiv 0 P)| ≤ |eval (ζ x) (pderiv 1 P)| := by
  have hzero : balance P (ζ x₀) ≤ 0 := sub_nonpos.mpr (sq_le_sq.mpr hinit)
  have hsign : SignType.sign (balance P (ζ x)) ≤ 0 := by
    rw [balance_sign P r s hs ζ hc hcurve x x₀ hx hx₀]
    exact sign_nonpos_iff.mpr hzero
  have hh := sign_nonpos_iff.mp hsign
  exact sq_le_sq.mp (sub_nonpos.mp hh)

theorem abs_ge_propagates (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (s : Set X)
    (hs : IsPreconnected s) (ζ : X → Fin 2 → ℝ) (hc : ContinuousOn ζ s)
    (hcurve : ∀ t ∈ s, eval (ζ t) P = 0 ∧ ζ t ∉ GraphControlExceptions.points P r)
    (x₀ : X) (hx₀ : x₀ ∈ s)
    (hinit : |eval (ζ x₀) (pderiv 1 P)| ≤ |eval (ζ x₀) (pderiv 0 P)|)
    (x : X) (hx : x ∈ s) : |eval (ζ x) (pderiv 1 P)| ≤ |eval (ζ x) (pderiv 0 P)| := by
  have hzero : 0 ≤ balance P (ζ x₀) := sub_nonneg.mpr (sq_le_sq.mpr hinit)
  have hsign : 0 ≤ SignType.sign (balance P (ζ x)) := by
    rw [balance_sign P r s hs ζ hc hcurve x x₀ hx hx₀]
    exact sign_nonneg_iff.mpr hzero
  have hh := sign_nonneg_iff.mp hsign
  exact sq_le_sq.mp (sub_nonneg.mp hh)

end PaperP1.GradientComparisonControl
