module

public import PaperP1.Algebra.FinitePlaneBezout
public import PaperP1.Algebra.BivariateCurveDegreeTransport
public import PaperP1.Algebra.SmoothPointAbsoluteIrreducibility

/-! # Height-free quadratic-degree bounds for non-geometric plane equations

The scalar extension is arbitrary. A base-field smooth point would force its
irreducibility, so the non-geometric case is an internally proved finite count.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonGeometricPlanePointBound

open Polynomial Finset PaperP1.BivariateCurveDegreeTransport
  PaperP1.PolynomialScalarProjection

variable {K : Type*} [Field K] [CharZero K]

theorem critical_points_card (P : K[X][X]) (hP : Irreducible P) (hdeg : 0 < P.natDegree)
    (S : Finset (K × K))
    (hS : ∀ p ∈ S, P.evalEval p.1 p.2 = 0 ∧ P.derivative.evalEval p.1 p.2 = 0) :
    S.card ≤ PlaneCurvePointCount.degree P * (PlaneCurvePointCount.degree P - 1) := by
  have hnot : ¬ P ∣ P.derivative := by
    intro hd
    have hne : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (ne_of_gt hdeg)
    exact (not_lt_of_ge (Polynomial.natDegree_le_of_dvd hd hne))
      (Polynomial.natDegree_derivative_lt (ne_of_gt hdeg))
  exact (FinitePlaneBezout.common_points_card P P.derivative hP hnot S hS).trans
    (Nat.mul_le_mul_left _ (degree_derivative P))

variable {L : Type*} [Field L] [Algebra K L]

theorem finite_points_card_of_outer_positive (P : K[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (hred : ¬Irreducible (extend P : L[X][X]))
    (S : Finset (K × K)) (hS : ∀ p ∈ S, P.evalEval p.1 p.2 = 0) :
    S.card ≤ PlaneCurvePointCount.degree P * (PlaneCurvePointCount.degree P - 1) := by
  apply critical_points_card P hP hdeg S
  intro p hp
  exact ⟨hS p hp, SmoothPointAbsoluteIrreducibility.derivative_zero_of_reducible
    P hP hdeg hred p.1 p.2 (hS p hp)⟩

theorem finite_points_card (P : K[X][X]) (hP : Irreducible P)
    (hred : ¬Irreducible (extend P : L[X][X]))
    (S : Finset (K × K)) (hS : ∀ p ∈ S, P.evalEval p.1 p.2 = 0) :
    S.card ≤ PlaneCurvePointCount.degree P * (PlaneCurvePointCount.degree P - 1) := by
  classical
  by_cases hempty : S = ∅
  · simp [hempty]
  by_cases hdeg : 0 < P.natDegree
  · exact finite_points_card_of_outer_positive P hP hdeg hred S hS
  obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hdpos := FinitePlaneBezout.positive_degree_of_zero P hP.ne_zero p₀.1 p₀.2 (hS p₀ hp₀)
  have hpartial := degree_le_partial_sum P
  have hswapdeg : 0 < (Bivariate.swap P).natDegree := by omega
  have hswapirr : Irreducible (Bivariate.swap P) :=
    (MulEquiv.irreducible_iff Bivariate.swap).mpr hP
  have hswapred : ¬Irreducible (extend (Bivariate.swap P) : L[X][X]) := by
    intro hi
    rw [extend_swap] at hi
    exact hred ((MulEquiv.irreducible_iff Bivariate.swap).mp hi)
  have hs : ∀ p ∈ S.image Prod.swap, (Bivariate.swap P).evalEval p.1 p.2 = 0 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    change (Bivariate.swap P).evalEval q.2 q.1 = 0
    rw [swap_evaluation]
    exact hS q hq
  have hb := finite_points_card_of_outer_positive (Bivariate.swap P) hswapirr hswapdeg
    hswapred (S.image Prod.swap) hs
  rw [Finset.card_image_of_injective S Prod.swap_injective, degree_swap] at hb
  exact hb

theorem grid_card (P : K[X][X]) (hP : Irreducible P)
    (hred : ¬Irreducible (extend P : L[X][X])) (B : ℕ) :
    (PlaneCurvePointCount.grid P B).card ≤
      PlaneCurvePointCount.degree P * (PlaneCurvePointCount.degree P - 1) := by
  classical
  let f : ℤ × ℤ → K × K := fun p ↦ ((p.1 : K), (p.2 : K))
  have hi : Function.Injective f := by
    intro p q he
    exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
      (Int.cast_injective (congrArg Prod.snd he))
  have hS : ∀ p ∈ (PlaneCurvePointCount.grid P B).image f, P.evalEval p.1 p.2 = 0 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact ((PlaneCurvePointCount.mem_grid P B q).mp hq).2.2
  have hb := finite_points_card P hP hred ((PlaneCurvePointCount.grid P B).image f) hS
  rwa [Finset.card_image_of_injective _ hi] at hb

end PaperP1.NonGeometricPlanePointBound
