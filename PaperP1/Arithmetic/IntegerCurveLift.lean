module

public import PaperP1.Algebra.LocalizationIrreducibleLift
public import PaperP1.Arithmetic.IntegerCurveRationalization
public import PaperP1.Algebra.FormalWordPolynomials

/-! # An actual irreducible rational plane equation has an irreducible integer model with the same integer points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCurveLift

open Polynomial PaperP1.BivariateDegrees PaperP1.FormalWordPolynomials

attribute [local instance] Polynomial.algebra

theorem exists_integer (f : ℚ[X][X]) (hf : Irreducible f) :
    ∃ P : ℤ[X][X], Irreducible P ∧ Associated (rationalize P) f := by
  let S : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map Polynomial.C
  let : IsLocalization S ℚ[X] := Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  let : IsLocalization (S.map Polynomial.C) ℚ[X][X] := Polynomial.isLocalization S ℚ[X]
  exact LocalizationIrreducibleLift.exists_associated (S.map Polynomial.C) f hf

theorem rationalize_swap (P : ℤ[X][X]) : rationalize (Bivariate.swap P) = Bivariate.swap (rationalize P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial m a =>
      simp only [rationalize, coe_mapRingHom, Polynomial.map_monomial, Bivariate.swap_monomial_monomial]

theorem degreeY_rationalize (P : ℤ[X][X]) : degreeY P = (rationalize P).natDegree := by
  have hinj : Function.Injective (Polynomial.mapRingHom (Int.castRingHom ℚ)) :=
    Polynomial.map_injective _ Int.cast_injective
  exact (natDegree_map_eq_of_injective hinj P).symm

theorem degreeX_rationalize (P : ℤ[X][X]) : degreeX P = (Bivariate.swap (rationalize P)).natDegree := by
  rw [degreeX, ← rationalize_swap]
  exact degreeY_rationalize _

theorem point_iff (P : ℤ[X][X]) (f : ℚ[X][X]) (hass : Associated (rationalize P) f) (x y : ℤ) :
    P.evalEval x y = 0 ↔ f.evalEval (x : ℚ) (y : ℚ) = 0 := by
  have hmap : (rationalize P).evalEval (x : ℚ) (y : ℚ) = ((P.evalEval x y : ℤ) : ℚ) := by
    simpa only [rationalize, coe_mapRingHom, Int.coe_castRingHom] using
      Polynomial.map_mapRingHom_evalEval (Int.castRingHom ℚ) P x y
  have h := (hass.map (Polynomial.evalEvalRingHom (x : ℚ) (y : ℚ))).eq_zero_iff
  change (rationalize P).evalEval (x : ℚ) (y : ℚ) = 0 ↔ f.evalEval (x : ℚ) (y : ℚ) = 0 at h
  rw [hmap, Int.cast_eq_zero] at h
  exact h

theorem partial_degree_bounds (P : ℤ[X][X]) (f : ℚ[X][X]) (hf0 : f ≠ 0)
    (hass : Associated (rationalize P) f) :
    degreeX P ≤ (Bivariate.swap f).natDegree ∧ degreeY P ≤ f.natDegree := by
  have hs0 : Bivariate.swap f ≠ 0 := by
    intro hz
    exact hf0 (Bivariate.swap.injective (hz.trans (map_zero Bivariate.swap).symm))
  constructor
  · rw [degreeX_rationalize]
    exact natDegree_le_of_dvd (_root_.map_dvd Bivariate.swap hass.dvd) hs0
  · rw [degreeY_rationalize]
    exact natDegree_le_of_dvd hass.dvd hf0

theorem exists_integer_model (f : ℚ[X][X]) (hf : Irreducible f) :
    ∃ P : ℤ[X][X], Irreducible P ∧ Associated (rationalize P) f ∧
      degreeX P ≤ (Bivariate.swap f).natDegree ∧ degreeY P ≤ f.natDegree ∧
      ∀ x y : ℤ, P.evalEval x y = 0 ↔ f.evalEval (x : ℚ) (y : ℚ) = 0 := by
  obtain ⟨P, hP, hass⟩ := exists_integer f hf
  obtain ⟨hx, hy⟩ := partial_degree_bounds P f hf.ne_zero hass
  exact ⟨P, hP, hass, hx, hy, point_iff P f hass⟩

end PaperP1.IntegerCurveLift
