module

public import PaperP1.Algebra.BivariateLinearShear
public import PaperP1.Algebra.RationalCurveCriticalPoints
public import Mathlib.Data.Fintype.EquivFin

/-! # A finite affine plane intersection bound by the total-degree product

An injective shear projection removes the extraneous fibre-degree factor in
the earlier resultant bound. The coefficient field is arbitrary and infinite.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePlaneBezout

open Polynomial Finset PaperP1.BivariateLinearShear

variable {F : Type*} [Field F]

theorem exists_injective_projection [Infinite F] (S : Finset (F × F)) :
    ∃ t : F, Set.InjOn (fun p : F × F ↦ p.1 + t * p.2) (S : Set (F × F)) := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    ((S ×ˢ S).image (fun pq ↦ (pq.2.1 - pq.1.1) / (pq.1.2 - pq.2.2)))
  refine ⟨t, ?_⟩
  intro p hp q hq he
  change p.1 + t * p.2 = q.1 + t * q.2 at he
  by_cases hy : p.2 = q.2
  · apply Prod.ext _ hy
    rw [hy] at he
    exact add_right_cancel he
  · have hden : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hy
    have htval : t = (q.1 - p.1) / (p.2 - q.2) := by
      apply (eq_div_iff hden).mpr
      calc
        t * (p.2 - q.2) = (p.1 + t * p.2) - (p.1 + t * q.2) := by ring
        _ = (q.1 + t * q.2) - (p.1 + t * q.2) := by rw [he]
        _ = q.1 - p.1 := by ring
    exact False.elim (ht (mem_image.mpr ⟨(p, q), mem_product.mpr ⟨hp, hq⟩, htval.symm⟩))

theorem positive_degree_of_zero (Q : F[X][X]) (hne : Q ≠ 0) (x y : F)
    (hzero : Q.evalEval x y = 0) : 0 < PlaneCurvePointCount.degree Q := by
  by_contra! hd
  have hout := (BivariateResultantDegree.outer_degree_le Q).trans hd
  have heout : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hout
  have hrow : Q.coeff 0 ≠ 0 := by
    intro hz
    apply hne
    simpa only [hz, map_zero] using heout
  have hin := BivariateResultantDegree.coefficient_row_degree Q 0 hrow
  have heinner : Q.coeff 0 = C ((Q.coeff 0).coeff 0) :=
    Polynomial.eq_C_of_natDegree_le_zero (by omega)
  have heconst : Q = C (C ((Q.coeff 0).coeff 0)) := heout.trans (congrArg C heinner)
  rw [heconst, Polynomial.evalEval_CC] at hzero
  apply hne
  rw [heconst, hzero, map_zero, map_zero]

theorem common_points_card [Infinite F] (P Q : F[X][X]) (hP : Irreducible P)
    (hnot : ¬ P ∣ Q) (S : Finset (F × F))
    (hS : ∀ p ∈ S, P.evalEval p.1 p.2 = 0 ∧ Q.evalEval p.1 p.2 = 0) :
    S.card ≤ PlaneCurvePointCount.degree P * PlaneCurvePointCount.degree Q := by
  classical
  by_cases hempty : S = ∅
  · simp [hempty]
  obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hQne : Q ≠ 0 := by
    intro hz
    apply hnot
    rw [hz]
    exact dvd_zero P
  have hQpos := positive_degree_of_zero Q hQne p₀.1 p₀.2 (hS p₀ hp₀).2
  obtain ⟨t, ht⟩ := exists_injective_projection S
  let f : F × F → F := fun p ↦ p.1 + t * p.2
  let P' := shear (-t) P
  let Q' := shear (-t) Q
  have hP' : Irreducible P' := (MulEquiv.irreducible_iff (shear (-t))).mpr hP
  have hnot' : ¬ P' ∣ Q' := by
    intro hd
    obtain ⟨A, hA⟩ := hd
    apply hnot
    refine ⟨(shear (-t)).symm A, ?_⟩
    have he := congrArg (shear (-t)).symm hA
    simpa only [P', Q', map_mul, AlgEquiv.symm_apply_apply] using he
  have hnew (p : F × F) (hp : p ∈ S) :
      P'.evalEval (f p) p.2 = 0 ∧ Q'.evalEval (f p) p.2 = 0 := by
    have hcoord : (p.1 + t * p.2) + (-t) * p.2 = p.1 := by ring
    simpa only [P', Q', f, shear_evaluation, hcoord] using hS p hp
  have hcard : S.card = (S.image f).card := (Finset.card_image_of_injOn ht).symm
  have hdegP : PlaneCurvePointCount.degree P' = PlaneCurvePointCount.degree P := shear_degree _ _
  have hdegQ : PlaneCurvePointCount.degree Q' = PlaneCurvePointCount.degree Q := shear_degree _ _
  by_cases houter : 0 < P'.natDegree
  · have hres := RationalCurveCriticalPoints.resultant_nonzero_of_not_dvd P' Q' hP' houter hnot'
    have hsub : S.image f ⊆ (P'.resultant Q').roots.toFinset := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hres).mpr
      exact RationalCurveCriticalPoints.common_point P' Q' houter (f p) p.2
        (hnew p hp).1 (hnew p hp).2
    calc
      S.card = (S.image f).card := hcard
      _ ≤ (P'.resultant Q').roots.toFinset.card := card_le_card hsub
      _ ≤ (P'.resultant Q').roots.card := Multiset.toFinset_card_le _
      _ ≤ (P'.resultant Q').natDegree := Polynomial.card_roots' _
      _ ≤ _ := BivariateResultantDegree.resultant_degree P' Q' _ _ hdegP.le hdegQ.le
  · have heP : P' = C (P'.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (by omega)
    have hrow : P'.coeff 0 ≠ 0 := by
      intro hz
      apply hP'.ne_zero
      simpa only [hz, map_zero] using heP
    have hsub : S.image f ⊆ (P'.coeff 0).roots.toFinset := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_roots hrow).mpr
      have he := (hnew p hp).1
      rwa [heP, Polynomial.evalEval_C] at he
    have hd := BivariateResultantDegree.coefficient_row_degree P' 0 hrow
    calc
      S.card = (S.image f).card := hcard
      _ ≤ (P'.coeff 0).roots.toFinset.card := card_le_card hsub
      _ ≤ (P'.coeff 0).roots.card := Multiset.toFinset_card_le _
      _ ≤ (P'.coeff 0).natDegree := Polynomial.card_roots' _
      _ ≤ PlaneCurvePointCount.degree P := by simpa only [zero_add, hdegP] using hd
      _ ≤ _ := by
        have hone : 1 ≤ PlaneCurvePointCount.degree Q := by omega
        have hmul := Nat.mul_le_mul_left (PlaneCurvePointCount.degree P)
          hone
        simpa only [mul_one] using hmul

end PaperP1.FinitePlaneBezout
