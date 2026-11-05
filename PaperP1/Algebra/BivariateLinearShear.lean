module

public import PaperP1.Algebra.BivariateTotalDegreeChart
public import PaperP1.Algebra.HomogeneousLinearShear

/-! # Affine coordinate shears preserve the actual bivariate total degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateLinearShear

open Polynomial MvPolynomial PaperP1.BivariateTotalDegreeChart

theorem linear_substitution_degree {R σ τ : Type*} [CommRing R]
    (v : σ → MvPolynomial τ R) (hv : ∀ i, (v i).totalDegree ≤ 1)
    (p : MvPolynomial σ R) : (MvPolynomial.aeval v p).totalDegree ≤ p.totalDegree := by
  classical
  have hm (d : σ →₀ ℕ) (a : R) :
      (MvPolynomial.aeval v (MvPolynomial.monomial d a)).totalDegree ≤ d.sum (fun _ e ↦ e) := by
    rw [MvPolynomial.aeval_monomial]
    change (MvPolynomial.C a * d.prod (fun i e ↦ v i ^ e)).totalDegree ≤ _
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    unfold Finsupp.prod Finsupp.sum
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum ?_)
    intro i _hi
    exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  exact (hm d (p.coeff d)).trans (MvPolynomial.le_totalDegree hd)

variable {F : Type*} [Field F]

theorem substitute_degree (v : Fin 1 → F) (p : MvPolynomial (Fin 2) F) :
    (HomogeneousLinearShear.substitute v p).totalDegree = p.totalDegree := by
  have hle (w : Fin 1 → F) (q : MvPolynomial (Fin 2) F) :
      (HomogeneousLinearShear.substitute w q).totalDegree ≤ q.totalDegree := by
    apply linear_substitution_degree
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  have he : HomogeneousLinearShear.substitute (-v) (HomogeneousLinearShear.substitute v p) = p := by
    change ((HomogeneousLinearShear.substitute (-v)).comp (HomogeneousLinearShear.substitute v)) p = p
    rw [HomogeneousLinearShear.substitute_add, neg_add_cancel, HomogeneousLinearShear.substitute_zero]
    rfl
  exact (hle v p).antisymm (by simpa only [he] using hle (-v) (HomogeneousLinearShear.substitute v p))

def shear (t : F) : F[X][X] ≃ₐ[F] F[X][X] :=
  (chart F).symm.trans ((HomogeneousLinearShear.equiv (fun _ : Fin 1 ↦ t)).trans (chart F))

theorem shear_degree (t : F) (P : F[X][X]) :
    PlaneCurvePointCount.degree (shear t P) = PlaneCurvePointCount.degree P := by
  change PlaneCurvePointCount.degree
    (chart F (HomogeneousLinearShear.substitute (fun _ : Fin 1 ↦ t) ((chart F).symm P))) = _
  rw [chart_degree, substitute_degree]
  have hc := chart_degree ((chart F).symm P)
  simpa only [AlgEquiv.apply_symm_apply] using hc.symm

theorem shear_evaluation (t x y : F) (P : F[X][X]) :
    (shear t P).evalEval x y = P.evalEval (x + t * y) y := by
  have he : (MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 ↦ x))).comp
      (HomogeneousLinearShear.substitute (fun _ : Fin 1 ↦ t)).toRingHom =
      MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 ↦ x + t * y)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [HomogeneousLinearShear.substitute]
    · intro i
      cases i using Fin.cases <;> simp [HomogeneousLinearShear.substitute]
  change (chart F (HomogeneousLinearShear.substitute (fun _ : Fin 1 ↦ t)
    ((chart F).symm P))).evalEval x y = _
  rw [chart_evaluation]
  change ((MvPolynomial.eval (Fin.cons y (fun _ : Fin 1 ↦ x))).comp
    (HomogeneousLinearShear.substitute (fun _ : Fin 1 ↦ t)).toRingHom) ((chart F).symm P) = _
  rw [he, ← chart_evaluation, AlgEquiv.apply_symm_apply]

end PaperP1.BivariateLinearShear
