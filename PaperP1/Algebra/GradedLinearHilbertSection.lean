module

public import PaperP1.Algebra.HomogeneousPrincipalQuotient
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic.Linarith

/-! # Actual homogeneous sections of a graded domain with a positive linear Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedLinearHilbertSection

open Polynomial

theorem eventual_dimension {F A : Type*} [Field F] [CommRing A] [Algebra F A] [IsDomain A]
    (H : ℕ → Submodule F A) [GradedAlgebra H] (d : ℕ) (hd : 0 < d) (b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial H (C (d : ℚ) * X + C b))
    {e : ℕ} {f : A} (hf : f ∈ H e) (hf0 : f ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      Module.finrank F (HomogeneousPrincipalQuotient.piece H f (n + e)) = e * d := by
  obtain ⟨N₀, hN₀⟩ := hp
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  obtain ⟨M, hM⟩ := exists_nat_gt (-b / (d : ℚ))
  have hMb : 0 < (d : ℚ) * (M : ℚ) + b := by
    have hh := (div_lt_iff₀ hdQ).mp hM
    nlinarith only [hh]
  refine ⟨max N₀ M, ?_⟩
  intro n hn
  have hnN : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have h₀ := hN₀ n hnN
  have h₁ := hN₀ (n + e) (by omega)
  simp only [eval_add, eval_mul, eval_C, eval_X, Nat.cast_add] at h₀ h₁
  have hnmQ : (M : ℚ) ≤ (n : ℚ) := by exact_mod_cast hnM
  have hposQ : (0 : ℚ) < (Module.finrank F (H (n + e)) : ℚ) := by
    have heQ : (0 : ℚ) ≤ e := Nat.cast_nonneg _
    nlinarith only [h₁, hMb, hnmQ, hdQ, heQ]
  let : Module.Finite F (H (n + e)) := Module.finite_of_finrank_pos (by exact_mod_cast hposQ)
  have hdim := HomogeneousPrincipalQuotient.finrank_add H hf hf0 n
  have hdimQ : (Module.finrank F (HomogeneousPrincipalQuotient.piece H f (n + e)) : ℚ) +
      (Module.finrank F (H n) : ℚ) = (Module.finrank F (H (n + e)) : ℚ) := by
    exact_mod_cast hdim
  have heq : (Module.finrank F (HomogeneousPrincipalQuotient.piece H f (n + e)) : ℚ) =
      ((e * d : ℕ) : ℚ) := by
    push_cast
    nlinarith only [h₀, h₁, hdimQ]
  exact_mod_cast heq

end PaperP1.GradedLinearHilbertSection
