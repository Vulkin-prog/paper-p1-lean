module

public import PaperP1.Algebra.BivariateTotalDegreeChart
public import PaperP1.Algebra.BivariateCurveDegreeTransport
public import PaperP1.Diophantine.ProjectiveSmoothDeterminant
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! # The actual finite-field class budget for a plane equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldPlaneZeroBound

open Polynomial Finset

theorem multivariate_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : MvPolynomial (Fin 2) F) (hP : P ≠ 0) (S : Finset (Fin 2 → F))
    (hS : ∀ z ∈ S, MvPolynomial.eval z P = 0) :
    S.card ≤ P.totalDegree * Fintype.card F := by
  classical
  let Z := (univ : Finset (Fin 2 → F)).filter (fun z ↦ MvPolynomial.eval z P = 0)
  have hsub : S ⊆ Z := fun z hz ↦ mem_filter.mpr ⟨mem_univ _, hS z hz⟩
  have hs : (Z.card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ 2 ≤
      (P.totalDegree : ℚ≥0) / (Fintype.card F : ℚ≥0) := by
    simpa only [Fintype.piFinset_univ, card_univ] using
      MvPolynomial.schwartz_zippel_totalDegree hP (univ : Finset F)
  have hN : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hm := (div_le_div_iff₀ (pow_pos hN 2) hN).mp hs
  have hm' : (Z.card : ℚ≥0) * Fintype.card F ≤
      ((P.totalDegree : ℚ≥0) * Fintype.card F) * Fintype.card F := by
    simpa only [pow_two, mul_assoc] using hm
  have hb : (Z.card : ℚ≥0) ≤ (P.totalDegree : ℚ≥0) * Fintype.card F :=
    (mul_le_mul_iff_of_pos_right hN).mp hm'
  have hn : Z.card ≤ P.totalDegree * Fintype.card F := by exact_mod_cast hb
  exact (card_le_card hsub).trans hn

theorem plane_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : F[X][X]) (hP : P ≠ 0) (S : Finset (F × F))
    (hS : ∀ z ∈ S, P.evalEval z.1 z.2 = 0) :
    S.card ≤ PlaneCurvePointCount.degree P * Fintype.card F := by
  classical
  let Q := (BivariateTotalDegreeChart.chart F).symm P
  let f : F × F → Fin 2 → F := fun z ↦ ![z.2, z.1]
  have hi : Function.Injective f := by
    intro z w he
    apply Prod.ext
    · exact congrFun he 1
    · exact congrFun he 0
  have hQ : Q ≠ 0 := by
    intro hz
    apply hP
    have he := congrArg (BivariateTotalDegreeChart.chart F) hz
    simpa only [Q, AlgEquiv.apply_symm_apply, map_zero] using he
  have he (z : F × F) : MvPolynomial.eval (f z) Q = P.evalEval z.1 z.2 := by
    have hb := BivariateTotalDegreeChart.chart_evaluation Q z.1 z.2
    rw [AlgEquiv.apply_symm_apply] at hb
    have hf : f z = Fin.cons z.2 (fun _ : Fin 1 ↦ z.1) := by
      funext i
      fin_cases i <;> rfl
    rw [hf]
    exact hb.symm
  have hc := multivariate_card Q hQ (S.image f) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    rw [he]
    exact hS w hw)
  have hd : Q.totalDegree = PlaneCurvePointCount.degree P := by
    rw [← BivariateTotalDegreeChart.chart_degree, AlgEquiv.apply_symm_apply]
  rw [card_image_of_injective _ hi, hd] at hc
  exact hc

theorem coefficient_map_degree_le {R F : Type*} [CommRing R] [CommRing F]
    (φ : R →+* F) (P : R[X][X]) :
    PlaneCurvePointCount.degree (P.map (Polynomial.mapRingHom φ)) ≤ PlaneCurvePointCount.degree P := by
  apply Finset.sup_le
  intro i hi
  have he : (P.map (Polynomial.mapRingHom φ)).coeff i = (P.coeff i).map φ := Polynomial.coeff_map _ _
  have hrow : P.coeff i ≠ 0 := by
    intro hz
    have hn := Polynomial.mem_support_iff.mp hi
    exact hn (by rw [he, hz, Polynomial.map_zero])
  have hd := Finset.le_sup (f := fun i ↦ i + (P.coeff i).natDegree) (Polynomial.mem_support_iff.mpr hrow)
  have hn : ((P.map (Polynomial.mapRingHom φ)).coeff i).natDegree ≤ (P.coeff i).natDegree := by
    rw [he]
    exact Polynomial.natDegree_map_le
  exact (Nat.add_le_add_left hn i).trans hd

theorem smooth_integer_classes_card (p : ℕ) (hp : p.Prime) (G : ℤ[X][X])
    (S : Finset (ZMod p × ZMod p))
    (hS : ∀ z ∈ S, BivariateEvaluation.evaluate z.1 z.2 G = 0 ∧
      BivariateEvaluation.evaluate z.1 z.2 G.derivative ≠ 0) :
    S.card ≤ (BivariateDegrees.degreeX G + BivariateDegrees.degreeY G) * p := by
  let : Fact p.Prime := ⟨hp⟩
  let P := G.map (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
  by_cases hP : P = 0
  · have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      apply (hS z hz).2
      have hd : P.derivative.evalEval z.1 z.2 = 0 := by
        rw [hP, Polynomial.derivative_zero]
        exact (Polynomial.evalEvalRingHom z.1 z.2).map_zero
      simpa only [P, Polynomial.derivative_map, ProjectiveSmoothDeterminant.coefficient_evaluation] using hd
    simp only [he, card_empty, Nat.zero_le]
  · have hc := plane_card P hP S (by
      intro z hz
      simpa only [P, ProjectiveSmoothDeterminant.coefficient_evaluation] using (hS z hz).1)
    have hd := (coefficient_map_degree_le (Int.castRingHom (ZMod p)) G).trans
      (BivariateCurveDegreeTransport.degree_le_partial_sum G)
    have hn := hc.trans (Nat.mul_le_mul_right (Fintype.card (ZMod p)) hd)
    simpa only [ZMod.card, BivariateDegrees.degreeX, BivariateDegrees.degreeY] using hn

end PaperP1.FiniteFieldPlaneZeroBound
