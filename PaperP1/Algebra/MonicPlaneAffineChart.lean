module

public import PaperP1.Algebra.HomogeneousAffinePrincipalChart
public import PaperP1.Algebra.HomogeneousAffineLineClassification
public import PaperP1.Algebra.BivariateTotalDegreeChart
public import PaperP1.Algebra.MvPolynomialSubstitutionDegree
public import PaperP1.Algebra.HomogeneousMonicGenerator
public import Mathlib.Tactic.FinCases

/-! # The actual middle-coordinate affine chart of a monic homogeneous plane equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonicPlaneAffineChart

open MvPolynomial

variable {F : Type*} [Field F]

def chart : MvPolynomial (Fin 3) F →ₐ[F] Polynomial (Polynomial F) :=
  aeval ![Polynomial.X, 1, Polynomial.C Polynomial.X]

def affine : MvPolynomial (Fin 3) F →ₐ[F] MvPolynomial (Fin 2) F :=
  aeval ![X 0, 1, X 1]

theorem chart_factor : chart (F := F) =
    (Polynomial.mapAlgHom (aeval (R := F) ![1, (Polynomial.X : Polynomial F)])).comp
      (finSuccEquiv F 2).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [chart, finSuccEquiv_X_zero]
  · change chart (X j.succ) = Polynomial.map _ (finSuccEquiv F 2 (X j.succ))
    rw [finSuccEquiv_X_succ, Polynomial.map_C]
    fin_cases j <;> simp [chart]

theorem chart_affine : chart (F := F) = (BivariateTotalDegreeChart.chart F).toAlgHom.comp affine := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chart, affine, BivariateTotalDegreeChart.chart_X_zero,
    BivariateTotalDegreeChart.chart_X_one]

theorem chart_native : (chart (F := F)).toRingHom = (NativeAffineChart.specialization F).comp
    (renameEquiv F (Equiv.swap (1 : Fin 3) 2)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change chart (C a) = NativeAffineChart.specialization F
      (renameEquiv F (Equiv.swap (1 : Fin 3) 2) (C a))
    simp [chart, HomogeneousAffineLineClassification.specialization_C]
  · intro i
    fin_cases i <;> simp [chart, RingHom.comp_apply, renameEquiv_apply, Equiv.swap_apply_def,
      HomogeneousAffineLineClassification.specialization_X,
      HomogeneousAffineLineClassification.specialization_Y,
      NativeVeroneseAffineIdeal.specialization_Z]

theorem evaluation (q : MvPolynomial (Fin 3) F) (x y : F) :
    (chart q).evalEval x y = eval ![y, 1, x] q := by
  have hh : (Polynomial.evalEvalRingHom x y).comp (chart (F := F)).toRingHom = eval ![y, 1, x] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply, chart]
    · intro i
      fin_cases i <;> simp [RingHom.comp_apply, chart]
  exact RingHom.congr_fun hh q

theorem degree_le (q : MvPolynomial (Fin 3) F) :
    PlaneCurvePointCount.degree (chart q) ≤ q.totalDegree := by
  rw [chart_affine]
  change PlaneCurvePointCount.degree (BivariateTotalDegreeChart.chart F (affine q)) ≤ _
  rw [BivariateTotalDegreeChart.chart_degree]
  have hh := MvPolynomialSubstitutionDegree.totalDegree_eval2_le (RingHom.id F)
    (![X 0, 1, X 1] : Fin 3 → MvPolynomial (Fin 2) F) 1 (by
      intro i
      fin_cases i <;> simp) q
  change ((eval₂Hom C ![X 0, 1, X 1]) q).totalDegree ≤ q.totalDegree
  simpa only [Nat.mul_one, RingHom.comp_id] using hh

theorem monic (q : MvPolynomial (Fin 3) F) (hq : (finSuccEquiv F 2 q).Monic) :
    (chart q).Monic := by
  rw [chart_factor]
  exact hq.map _

theorem natDegree (q : MvPolynomial (Fin 3) F) (hq : (finSuccEquiv F 2 q).Monic) :
    (chart q).natDegree = (finSuccEquiv F 2 q).natDegree := by
  rw [chart_factor]
  exact hq.natDegree_map _

theorem natDegree_le_planeDegree (P : Polynomial (Polynomial F)) :
    P.natDegree ≤ PlaneCurvePointCount.degree P := by
  by_cases hP : P = 0
  · simp [hP]
  have hm : P.natDegree ∈ P.support := Polynomial.natDegree_mem_support_of_ne_zero hP
  exact (Nat.le_add_right _ _).trans (Finset.le_sup (f := fun i ↦ i + (P.coeff i).natDegree) hm)

theorem degree_eq (q : MvPolynomial (Fin 3) F) (hq : (finSuccEquiv F 2 q).Monic)
    {d : ℕ} (hdegree : q.totalDegree = d) (houter : (finSuccEquiv F 2 q).natDegree = d) :
    PlaneCurvePointCount.degree (chart q) = d := by
  apply le_antisymm
  · exact (degree_le q).trans_eq hdegree
  · rw [← houter, ← natDegree q hq]
    exact natDegree_le_planeDegree _

theorem degree_of_homogeneous_monic (q : MvPolynomial (Fin 3) F)
    (hq : (finSuccEquiv F 2 q).Monic) {d : ℕ} (hhom : q.IsHomogeneous d) :
    PlaneCurvePointCount.degree (chart q) = d := by
  have hq0 : q ≠ 0 := fun hz ↦ hq.ne_zero (by rw [hz, map_zero])
  have hh := HomogeneousMonicGenerator.homogeneous q
    (PlaneCurveHilbert.ideal_homogeneous F q hhom) hq
  apply degree_eq q hq (hhom.totalDegree hq0)
  exact (hh.totalDegree hq0).symm.trans (hhom.totalDegree hq0)

theorem irreducible (q : MvPolynomial (Fin 3) F) (hq : Irreducible q) {d : ℕ}
    (hhom : q.IsHomogeneous d) (hchart : X (1 : Fin 3) ∉ Ideal.span {q}) :
    Irreducible (chart q) := by
  let e := renameEquiv F (Equiv.swap (1 : Fin 3) 2)
  have hq' : Irreducible (e q) := (MulEquiv.irreducible_iff e).mpr hq
  let : Fact (Irreducible (e q)) := ⟨hq'⟩
  have hhom' : (e q).IsHomogeneous d := hhom.rename_isHomogeneous
  have hchart' : X (2 : Fin 3) ∉ HomogeneousPrincipalQuotient.ideal (e q) := by
    intro hh
    apply hchart
    apply Ideal.mem_span_singleton.mpr
    have hdvd : e q ∣ X (2 : Fin 3) := Ideal.mem_span_singleton.mp hh
    have he := map_dvd e.symm hdvd
    change e.symm (e q) ∣ e.symm (X (2 : Fin 3)) at he
    rw [e.symm_apply_apply] at he
    simpa [e, renameEquiv_symm, renameEquiv_apply] using he
  have hh := HomogeneousAffinePrincipalChart.affine_irreducible (e q) hhom' hchart'
  change Irreducible (NativeAffineChart.specialization F (e q)) at hh
  have he := RingHom.congr_fun (chart_native (F := F)) q
  exact he.symm ▸ hh

end PaperP1.MonicPlaneAffineChart
