module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Data.Rat.Defs

/-! # Hilbert polynomials and their multiplicity for actual homogeneous pieces

The numerical function in this definition is the dimension of the given
submodules. Existence is an explicit argument; uniqueness is proved from
infinitely many natural evaluations. No existence theorem for general graded
algebras, scheme intersection theory, or host-count estimate is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedHilbertPolynomial

variable {F A : Type*} [Field F] [AddCommGroup A] [Module F A]

def IsHilbertPolynomial (G : ℕ → Submodule F A) (p : Polynomial ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (Module.finrank F (G n) : ℚ)

theorem unique {G : ℕ → Submodule F A} {p q : Polynomial ℚ}
    (hp : IsHilbertPolynomial G p) (hq : IsHilbertPolynomial G q) : p = q := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hq
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite (max N M)).image
    (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨n, hn, rfl⟩
  change p.eval (n : ℚ) = q.eval (n : ℚ)
  rw [hN n ((le_max_left N M).trans hn), hM n ((le_max_right N M).trans hn)]

def polynomial (G : ℕ → Submodule F A) (h : ∃ p, IsHilbertPolynomial G p) : Polynomial ℚ :=
  h.choose

theorem polynomial_eq (G : ℕ → Submodule F A) (h : ∃ p, IsHilbertPolynomial G p)
    (p : Polynomial ℚ) (hp : IsHilbertPolynomial G p) : polynomial G h = p :=
  unique h.choose_spec hp

def multiplicity (G : ℕ → Submodule F A) (h : ∃ p, IsHilbertPolynomial G p) : ℚ :=
  ((polynomial G h).natDegree.factorial : ℚ) * (polynomial G h).leadingCoeff

theorem multiplicity_eq (G : ℕ → Submodule F A) (h : ∃ p, IsHilbertPolynomial G p)
    (p : Polynomial ℚ) (hp : IsHilbertPolynomial G p) :
    multiplicity G h = (p.natDegree.factorial : ℚ) * p.leadingCoeff := by
  rw [multiplicity, polynomial_eq G h p hp]

end PaperP1.GradedHilbertPolynomial
