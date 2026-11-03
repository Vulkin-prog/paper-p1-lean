module

public import PaperP1.Algebra.HomogeneousPrincipalQuotient
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # An actual constant hyperplane quotient Hilbert function gives an affine Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedHilbertHyperplane

open Polynomial

theorem affine_of_difference (h : ℕ → ℕ) (N c : ℕ)
    (hs : ∀ n : ℕ, N ≤ n → h (n + 1) = h n + c) :
    ∀ n : ℕ, N ≤ n → h n = h N + (n - N) * c := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [hs n hn, ih]
    have he : n + 1 - N = (n - N) + 1 := by omega
    rw [he, add_mul, one_mul, add_assoc]

variable {F B : Type*} [Field F] [CommRing B] [Algebra F B] [IsDomain B]
  (H : ℕ → Submodule F B) [GradedAlgebra H] {b : B} (hb : b ∈ H 1) (hb0 : b ≠ 0)

include hb hb0 in
theorem exists_polynomial [∀ n, Module.Finite F (H n)]
    (hc : ∃ M c : ℕ, ∀ n : ℕ, M ≤ n →
      Module.finrank F (HomogeneousPrincipalQuotient.piece H b n) = c) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial H p := by
  obtain ⟨N, c, hN⟩ := hc
  have hs (n : ℕ) (hn : N ≤ n) : Module.finrank F (H (n + 1)) = Module.finrank F (H n) + c := by
    have he := HomogeneousPrincipalQuotient.finrank_add H hb hb0 n
    rw [hN (n + 1) (hn.trans (Nat.le_add_right n 1))] at he
    exact he.symm.trans (Nat.add_comm _ _)
  refine ⟨C (c : ℚ) * X + C ((Module.finrank F (H N) : ℚ) - (c : ℚ) * (N : ℚ)), N, fun n hn ↦ ?_⟩
  have he := congrArg (Nat.cast : ℕ → ℚ) (affine_of_difference (fun n ↦ Module.finrank F (H n)) N c hs n hn)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hn] at he
  simp only [eval_add, eval_mul, eval_C, eval_X]
  nlinarith

end PaperP1.GradedHilbertHyperplane
