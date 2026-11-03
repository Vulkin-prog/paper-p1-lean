module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring

/-! # Nonvanishing of a homogeneous polynomial on a fixed affine projective chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousPolynomialEvaluation

open MvPolynomial

variable {F σ : Type*} [CommSemiring F]

/-- Scaling the input multiplies an actual homogeneous polynomial by its degree power. -/
theorem eval_scale {e : ℕ} (p : MvPolynomial σ F) (hp : p.IsHomogeneous e)
    (t : F) (v : σ → F) : eval (fun i ↦ t * v i) p = t ^ e * eval v p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | add p q _ _ ihp ihq => rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial d c hd =>
    have hd' : d.degree = e := by rw [Finsupp.degree_eq_weight_one]; exact hd
    have ht : d.prod (fun _ n ↦ t ^ n) = t ^ e := by
      rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hd']
    simp only [eval_monomial, mul_pow, Finsupp.prod_mul, ht]
    ring

theorem homogeneous_zero_eq_C (p : MvPolynomial σ F) (hp : p.IsHomogeneous 0) :
    p = C (p.coeff 0) := by
  exact totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous σ).mpr hp)

variable {F : Type*} [Field F] [Infinite F]

/-- Every nonzero homogeneous polynomial is nonzero somewhere on the fixed patch X₀ = 1. -/
theorem exists_eval_cons_one {n e : ℕ} (p : MvPolynomial (Fin (n + 1)) F)
    (hp : p.IsHomogeneous e) (hp0 : p ≠ 0) :
    ∃ v : Fin n → F, eval (Fin.cons 1 v) p ≠ 0 := by
  classical
  have hprod : p * X 0 ≠ 0 := mul_ne_zero hp0 (X_ne_zero 0)
  obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1) → F, eval v (p * X 0) ≠ 0 := by
    by_contra! h
    exact hprod ((hp.mul (isHomogeneous_X F 0)).eq_zero_of_forall_eval_eq_zero h)
  simp only [map_mul, eval_X] at hv
  obtain ⟨hpv, hv0⟩ := mul_ne_zero_iff.mp hv
  let w (i : Fin n) := (v 0)⁻¹ * v i.succ
  have he : (fun i ↦ (v 0)⁻¹ * v i) = Fin.cons 1 w := by
    funext i
    cases i using Fin.cases with
    | zero => simp only [Fin.cons_zero, inv_mul_cancel₀ hv0]
    | succ i => rfl
  refine ⟨w, ?_⟩
  rw [← he, eval_scale p hp]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hv0)) hpv

end PaperP1.HomogeneousPolynomialEvaluation
