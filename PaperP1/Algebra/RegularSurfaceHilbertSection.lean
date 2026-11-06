module

public import PaperP1.Algebra.RegularGradedHilbertSection
public import PaperP1.Algebra.QuadraticHilbertDifference

/-! # Actual regular surface sections have the exact linear Hilbert degree equal to the equation degree times the surface degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularSurfaceHilbertSection

open Polynomial

theorem polynomial_difference {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (p : ℚ[X]) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H p)
    {e : ℕ} {f : A} (hf : f ∈ H e) (hregular : Function.Injective (fun a : A ↦ a * f)) :
    GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousPrincipalQuotient.piece H f)
      (QuadraticHilbertDifference.difference p e) := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨N + e, fun n hn ↦ ?_⟩
  let m := n - e
  have hen : e ≤ n := by omega
  have hmN : N ≤ m := by dsimp [m]; omega
  have hm : m + e = n := Nat.sub_add_cancel hen
  have hdim := RegularGradedHilbertSection.finrank_add H hf hregular m
  rw [hm] at hdim
  have hdQ : (Module.finrank F (HomogeneousPrincipalQuotient.piece H f n) : ℚ) +
      (Module.finrank F (H m) : ℚ) = (Module.finrank F (H n) : ℚ) := by exact_mod_cast hdim
  calc
    (QuadraticHilbertDifference.difference p e).eval (n : ℚ) = p.eval (n : ℚ) - p.eval (m : ℚ) := by
      simp only [QuadraticHilbertDifference.difference, eval_sub, eval_comp, eval_X, eval_C]
      rw [show (m : ℚ) = (n : ℚ) - (e : ℚ) by exact Nat.cast_sub hen]
    _ = (Module.finrank F (HomogeneousPrincipalQuotient.piece H f n) : ℚ) := by
      rw [hN n (by omega), hN m hmN]
      linarith

theorem linear_hilbert {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (p : ℚ[X]) (hpdeg : p.natDegree ≤ 2) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H p)
    (d : ℕ) (hcoeff : p.coeff 2 = (d : ℚ) / 2)
    {e : ℕ} {f : A} (hf : f ∈ H e) (hregular : Function.Injective (fun a : A ↦ a * f)) :
    GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousPrincipalQuotient.piece H f)
      (C ((e * d : ℕ) : ℚ) * X + C ((e : ℚ) * p.coeff 1 - (e : ℚ) ^ 2 * p.coeff 2)) := by
  have hh := polynomial_difference H p hp hf hregular
  have hc : 2 * (e : ℚ) * p.coeff 2 = ((e * d : ℕ) : ℚ) := by
    rw [hcoeff]
    push_cast
    ring
  rw [QuadraticHilbertDifference.expansion p hpdeg e, hc] at hh
  exact hh

end PaperP1.RegularSurfaceHilbertSection
