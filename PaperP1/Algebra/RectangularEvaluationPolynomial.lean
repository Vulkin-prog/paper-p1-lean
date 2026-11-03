module

public import PaperP1.Algebra.FiniteEvaluationAnnihilator
public import Mathlib.Algebra.Polynomial.Bivariate

/-! # Literal auxiliary polynomials from rectangular evaluation vectors

A rectangle of side d+1 gives a polynomial of total degree at most 2d.
Its dimension grows quadratically while that degree grows linearly.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RectangularEvaluationPolynomial

open Finset Polynomial

abbrev Index (d : ℕ) := Fin (d + 1) × Fin (d + 1)

variable {K : Type*} [Field K]

def row (d : ℕ) (x y : K) : Index d → K := fun i ↦ x ^ i.1.val * y ^ i.2.val

def polynomial (d : ℕ) (w : Index d → K) : K[X][X] :=
  ∑ b : Fin (d + 1), monomial b.val (∑ a : Fin (d + 1), monomial a.val (w (a, b)))

theorem outer_coefficient (d : ℕ) (w : Index d → K) (b : Fin (d + 1)) :
    (polynomial d w).coeff b.val = ∑ a : Fin (d + 1), monomial a.val (w (a, b)) := by
  classical
  simp [polynomial, coeff_monomial, Fin.val_inj]

theorem coefficient (d : ℕ) (w : Index d → K) (a b : Fin (d + 1)) :
    ((polynomial d w).coeff b.val).coeff a.val = w (a, b) := by
  classical
  simp [polynomial, coeff_monomial, Fin.val_inj]

theorem nonzero (d : ℕ) (w : Index d → K) (hw : w ≠ 0) : polynomial d w ≠ 0 := by
  intro h
  apply hw
  funext i
  have hc := congrArg (fun P : K[X][X] ↦ (P.coeff i.2.val).coeff i.1.val) h
  simpa only [coefficient, coeff_zero, Pi.zero_apply] using hc

theorem outer_degree (d : ℕ) (w : Index d → K) : (polynomial d w).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro b _
  exact (natDegree_monomial_le _).trans (by omega)

theorem inner_degree (d : ℕ) (w : Index d → K) (b : ℕ) :
    ((polynomial d w).coeff b).natDegree ≤ d := by
  classical
  by_cases hb : b < d + 1
  · rw [show b = (⟨b, hb⟩ : Fin (d + 1)).val from rfl, outer_coefficient]
    apply natDegree_sum_le_of_forall_le
    intro a _
    exact (natDegree_monomial_le _).trans (by omega)
  · rw [coeff_eq_zero_of_natDegree_lt ((outer_degree d w).trans_lt (by omega)), natDegree_zero]
    exact Nat.zero_le d

theorem total_degree (d : ℕ) (w : Index d → K) :
    (polynomial d w).support.sup (fun b ↦ b + ((polynomial d w).coeff b).natDegree) ≤ 2 * d := by
  apply Finset.sup_le
  intro b hb
  have hb₀ := le_natDegree_of_ne_zero (mem_support_iff.mp hb)
  have houter := outer_degree d w
  have hinner := inner_degree d w b
  omega

theorem evaluation (d : ℕ) (w : Index d → K) (x y : K) :
    (polynomial d w).evalEval x y = ∑ i : Index d, row d x y i * w i := by
  rw [← eval₂_evalRingHom]
  change (eval₂RingHom (evalRingHom x) y) (polynomial d w) = _
  simp only [polynomial, map_sum, coe_eval₂RingHom, eval₂_monomial,
    coe_evalRingHom, eval_monomial, Fintype.sum_prod_type, row]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  ring

theorem exists_polynomial {ι : Type*} (d : ℕ) (x y : ι → K)
    (hdet : ∀ f : Index d → ι, Function.Injective f →
      Matrix.det (fun i j ↦ row d (x (f i)) (y (f i)) j) = 0) :
    ∃ P : K[X][X], P ≠ 0 ∧ P.natDegree ≤ d ∧ (∀ b, (P.coeff b).natDegree ≤ d) ∧
      P.support.sup (fun b ↦ b + (P.coeff b).natDegree) ≤ 2 * d ∧
      ∀ i, P.evalEval (x i) (y i) = 0 := by
  obtain ⟨w, hw, he⟩ := FiniteEvaluationAnnihilator.coefficients (fun i ↦ row d (x i) (y i)) hdet
  refine ⟨polynomial d w, nonzero d w hw, outer_degree d w, inner_degree d w,
    total_degree d w, ?_⟩
  intro i
  rw [evaluation]
  exact he i

end PaperP1.RectangularEvaluationPolynomial
