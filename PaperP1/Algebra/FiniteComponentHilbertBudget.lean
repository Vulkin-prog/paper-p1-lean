module

public import PaperP1.Algebra.HomogeneousPrimeSeparators
public import PaperP1.Algebra.GradedSeparatedComponentPieces
public import PaperP1.Algebra.PolynomialEventualCoefficientOrder
public import Mathlib.Tactic.ComputeDegree

/-! # Genuine top Hilbert coefficients of finitely many incomparable prime components sum to at most the whole coefficient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteComponentHilbertBudget

open Polynomial Finset

theorem sum_coefficient_le {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (I : Ideal A) (Q : ι → Ideal A) (hprime : ∀ i, (Q i).IsPrime)
    (hhom : ∀ i, (Q i).IsHomogeneous H) (hinc : ∀ i j, j ≠ i → ¬ Q j ≤ Q i)
    (hIQ : ∀ i, I ≤ Q i) (p : ℚ[X]) (q : ι → ℚ[X]) (r : ℕ)
    (hpdeg : p.natDegree ≤ r) (hqdeg : ∀ i, (q i).natDegree ≤ r)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece H I) p)
    (hq : ∀ i, GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece H (Q i)) (q i)) :
    (∑ i, (q i).coeff r) ≤ p.coeff r := by
  classical
  obtain ⟨w, f, hf⟩ := HomogeneousPrimeSeparators.finite_family H Q hprime hhom hinc
  obtain ⟨N, hN⟩ := hp
  choose M hM using hq
  let L : ℚ[X] := ∑ i, (q i).comp (X + C (-(w i : ℚ)))
  let T := max N (univ.sup (fun i ↦ M i + w i))
  have hLdeg : L.natDegree ≤ r := natDegree_sum_le_of_forall_le _ _ (fun i _hi ↦
    PolynomialEventualCoefficientOrder.translation_degree_le (q i) _ r (hqdeg i))
  have htail : ∀ n : ℕ, T ≤ n → L.eval (n : ℚ) ≤ p.eval (n : ℚ) := by
    intro n hn
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnM (i : ι) : M i + w i ≤ n :=
      (Finset.le_sup (f := fun i ↦ M i + w i) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)
    have hnw (i : ι) : w i ≤ n := (Nat.le_add_left _ _).trans (hnM i)
    have heval : L.eval (n : ℚ) =
        ∑ i, (Module.finrank F (HomogeneousQuotientGrading.piece H (Q i) (n - w i)) : ℚ) := by
      rw [show L = ∑ i, (q i).comp (X + C (-(w i : ℚ))) from rfl, eval_finsetSum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [eval_comp, eval_add, eval_X, eval_C]
      rw [← sub_eq_add_neg]
      rw [← Nat.cast_sub (hnw i), hM i (n - w i) (by have := hnM i; omega)]
    rw [heval, hN n hnN]
    exact_mod_cast GradedSeparatedComponentPieces.dimension_le H I Q hprime hIQ w f
      (fun i ↦ (hf i).1) (fun i ↦ (hf i).2.1) (fun i j hij ↦ (hf i).2.2 j hij) n hnw
  have hh := PolynomialEventualCoefficientOrder.coefficient_le L p r hLdeg hpdeg T htail
  have hcoeff : L.coeff r = ∑ i, (q i).coeff r := by
    rw [show L = ∑ i, (q i).comp (X + C (-(w i : ℚ))) from rfl, finsetSum_coeff]
    exact Finset.sum_congr rfl (fun i _hi ↦
      PolynomialEventualCoefficientOrder.translation_coefficient (q i) _ r (hqdeg i))
  rwa [hcoeff] at hh

theorem sum_linear_degree_le {F A ι : Type*} [Field F] [CommRing A] [Algebra F A] [Fintype ι]
    (H : ℕ → Submodule F A) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (I : Ideal A) (Q : ι → Ideal A) (hprime : ∀ i, (Q i).IsPrime)
    (hhom : ∀ i, (Q i).IsHomogeneous H) (hinc : ∀ i j, j ≠ i → ¬ Q j ≤ Q i)
    (hIQ : ∀ i, I ≤ Q i) (d b : ℚ) (e β : ι → ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece H I)
      (C d * X + C b))
    (hq : ∀ i, GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece H (Q i))
      (C (e i) * X + C (β i))) : (∑ i, e i) ≤ d := by
  have hh := sum_coefficient_le H I Q hprime hhom hinc hIQ
    (C d * X + C b) (fun i ↦ C (e i) * X + C (β i)) 1 (by compute_degree)
    (fun _i ↦ by compute_degree) hp hq
  simpa only [coeff_add, coeff_C_mul, coeff_X_one, coeff_C_succ, mul_one, add_zero] using hh

end PaperP1.FiniteComponentHilbertBudget
