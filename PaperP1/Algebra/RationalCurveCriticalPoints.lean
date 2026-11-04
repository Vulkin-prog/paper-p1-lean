module

public import PaperP1.Algebra.BivariateResultantNonzero
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # An unconditional finite count of critical points on an irreducible affine curve

This supplies the numerical part of a possible non-geometric biform reduction.
It does not assume or prove that non-geometric curves have only singular
rational points. No existing ordinary input is discharged by this module alone.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalCurveCriticalPoints

open Polynomial Finset

variable {F : Type*} [Field F]

theorem resultant_nonzero_of_not_dvd (P Q : F[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (hnot : ¬P ∣ Q) : P.resultant Q ≠ 0 := by
  let K := FractionRing F[X]
  let φ : F[X] →+* K := algebraMap F[X] K
  have hinj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hprim : P.IsPrimitive := hP.isPrimitive (ne_of_gt hdeg)
  have hirr : Irreducible (P.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hnd : ¬P.map φ ∣ Q.map φ := by
    intro h
    exact hnot ((hprim.dvd_iff_fraction_map_dvd_fraction_map K).mpr h)
  have hcop : IsCoprime (P.map φ) (Q.map φ) := hirr.coprime_iff_not_dvd.mpr hnd
  have hn := Polynomial.resultant_ne_zero (P.map φ) (Q.map φ) hcop
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hn
  intro hz
  apply hn
  rw [Polynomial.resultant_map_map, hz, map_zero]

theorem specialization_nonzero (P : F[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (x : F) : P.map (evalRingHom x) ≠ 0 := by
  intro hz
  have hprim := hP.isPrimitive (ne_of_gt hdeg)
  apply not_isUnit_X_sub_C x
  apply hprim (X - C x)
  apply (C_dvd_iff_dvd_coeff _ _).mpr
  intro i
  apply dvd_iff_isRoot.mpr
  change (P.coeff i).eval x = 0
  have hc := congrArg (fun q : F[X] ↦ q.coeff i) hz
  simpa only [coeff_map, coeff_zero, coe_evalRingHom] using hc

theorem common_point (P Q : F[X][X]) (hdeg : 0 < P.natDegree)
    (x y : F) (hP : P.evalEval x y = 0) (hQ : Q.evalEval x y = 0) :
    (P.resultant Q).eval x = 0 := by
  obtain ⟨a, b, _ha, _hb, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    P Q le_rfl le_rfl (Or.inl (ne_of_gt hdeg))
  have h := congrArg (Polynomial.evalEvalRingHom x y) hbez
  simp only [map_add, map_mul, coe_evalEvalRingHom, hP, hQ, zero_mul,
    zero_add, evalEval_C] at h
  exact h.symm

theorem fibre_card (P : F[X][X]) (hP : Irreducible P) (hdeg : 0 < P.natDegree)
    (x : F) (S : Finset F) (hS : ∀ y ∈ S, P.evalEval x y = 0) :
    S.card ≤ P.natDegree := by
  classical
  have hsub : S ⊆ (P.map (evalRingHom x)).roots.toFinset := by
    intro y hy
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (specialization_nonzero P hP hdeg x)).mpr
    change (P.map (evalRingHom x)).eval y = 0
    simpa only [Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hS y hy
  calc
    _ ≤ (P.map (evalRingHom x)).roots.toFinset.card := card_le_card hsub
    _ ≤ (P.map (evalRingHom x)).roots.card := Multiset.toFinset_card_le _
    _ ≤ (P.map (evalRingHom x)).natDegree := Polynomial.card_roots' _
    _ ≤ _ := Polynomial.natDegree_map_le

theorem common_points_card (P Q : F[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (hnot : ¬P ∣ Q) (S : Finset (F × F))
    (hS : ∀ p ∈ S, P.evalEval p.1 p.2 = 0 ∧ Q.evalEval p.1 p.2 = 0) :
    S.card ≤ (P.resultant Q).natDegree * P.natDegree := by
  classical
  have hx : S.image Prod.fst ⊆ (P.resultant Q).roots.toFinset := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots
      (resultant_nonzero_of_not_dvd P Q hP hdeg hnot)).mpr
        (common_point P Q hdeg p.1 p.2 (hS p hp).1 (hS p hp).2))
  have hxcard : (S.image Prod.fst).card ≤ (P.resultant Q).natDegree :=
    (card_le_card hx).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
  have hfibre : ∀ x : F, (S.filter fun p ↦ p.1 = x).card ≤ P.natDegree := by
    intro x
    let T := S.filter fun p ↦ p.1 = x
    have hinj : Set.InjOn (fun p : F × F ↦ p.2) (T : Set (F × F)) := by
      intro p hp q hq he
      apply Prod.ext
      · exact (mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm
      · exact he
    rw [← card_image_of_injOn hinj]
    apply fibre_card P hP hdeg x
    intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hy
    obtain ⟨hpS, hpx⟩ := mem_filter.mp hp
    simpa only [hpx] using (hS p hpS).1
  calc
    _ = ∑ x ∈ S.image Prod.fst, (S.filter fun p ↦ p.1 = x).card :=
      card_eq_sum_card_image _ _
    _ ≤ ∑ _x ∈ S.image Prod.fst, P.natDegree := sum_le_sum (fun x _ ↦ hfibre x)
    _ = (S.image Prod.fst).card * P.natDegree := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hxcard

theorem derivative_resultant_nonzero [CharZero F] (P : F[X][X])
    (hP : Irreducible P) (hdeg : 0 < P.natDegree) : P.resultant P.derivative ≠ 0 := by
  apply resultant_nonzero_of_not_dvd P P.derivative hP hdeg
  intro hd
  have hne : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hdeg)
  exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd hd hne))
    (Polynomial.natDegree_derivative_lt (ne_of_gt hdeg))

theorem critical_points_card [CharZero F] (P : F[X][X])
    (hP : Irreducible P) (hdeg : 0 < P.natDegree) (S : Finset (F × F))
    (hS : ∀ p ∈ S, P.evalEval p.1 p.2 = 0 ∧ P.derivative.evalEval p.1 p.2 = 0) :
    S.card ≤ (P.resultant P.derivative).natDegree * P.natDegree := by
  apply common_points_card P P.derivative hP hdeg _ S hS
  intro hd
  have hne : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hdeg)
  exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd hd hne))
    (Polynomial.natDegree_derivative_lt (ne_of_gt hdeg))

end PaperP1.RationalCurveCriticalPoints
