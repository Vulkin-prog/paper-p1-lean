module

public import PaperP1.Geometry.ProjRadicalFieldChartLift
public import PaperP1.Geometry.IntegerCoefficientProjectiveMorphism
public import PaperP1.Algebra.P3FactorSegreEvaluation
public import PaperP1.Geometry.P3FactorMultiplicationProper
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-! # Actual projective factor-image membership gives literal factors over an algebraically closed field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FactorImageFactorization

open AlgebraicGeometry MvPolynomial P3HomogeneousCoefficientFamily P3FactorSegreGrading
open scoped Classical

attribute [local instance] MvPolynomial.gradedAlgebra P3FactorSegreGrading.grading

variable {F : Type} [Field F] [IsAlgClosed F]

theorem normalized_factors (e f : ℕ) (w : Index (e + f) → F) (hw : w ≠ 0)
    (himage : IntegerCoefficientProjectivePoint.point w hw ∈
      Set.range (P3FactorMultiplicationMap.multiplication e f)) :
    ∃ i : Index (e + f), w i ≠ 0 ∧
      ∃ (a : Index e → F) (b : Index f → F), a ≠ 0 ∧ b ≠ 0 ∧
        P3FactorSegreFieldPoint.productVector e f a b = fun m ↦ w m / w i := by
  obtain ⟨i, hi0⟩ := Function.ne_iff.mp hw
  have hi : w i ≠ 0 := by simpa only [Pi.zero_apply] using hi0
  let ε := IntegerCoefficientProjectiveMorphism.evaluation w
  have hε : ε (X i) ≠ 0 := by simpa only [ε, IntegerCoefficientProjectiveMorphism.evaluation_X] using hi
  let : LocallyOfFiniteType
      (ProjRadicalMap.map (gradedMap e f) (irrelevant_le_radical e f)) :=
    (P3FactorMultiplicationProper.multiplication_proper e f).toLocallyOfFiniteType
  have hy : GradedFieldChartEvaluation.pointMap (homogeneousSubmodule (Index (e + f)) ℤ)
      ε hε (isHomogeneous_X ℤ i) (IsLocalRing.closedPoint F) ∈
      Set.range (ProjRadicalMap.map (gradedMap e f) (irrelevant_le_radical e f)) := by
    change IntegerCoefficientProjectiveMorphism.map w i hi (IsLocalRing.closedPoint F) ∈
      Set.range (P3FactorMultiplicationMap.multiplication e f)
    rw [IntegerCoefficientProjectiveMorphism.map_closedPoint w hw i hi]
    exact himage
  obtain ⟨ρ, hρ⟩ := ProjRadicalFieldChartLift.exists_homogeneous_lift
    (gradedMap e f) (irrelevant_le_radical e f) ε hε (isHomogeneous_X ℤ i) hy
  have hcoeff (m : Index (e + f)) : ρ (coefficient e f m) = w m / w i := by
    have hh := hρ 1 (X m) (isHomogeneous_X ℤ m)
    simpa only [gradedMap_X, ε, IntegerCoefficientProjectiveMorphism.evaluation_X, pow_one] using hh
  have hn : (fun m ↦ ρ (coefficient e f m)) ≠ 0 := by
    intro hz
    have hh := congr_fun hz i
    rw [hcoeff i, div_self hi] at hh
    exact one_ne_zero hh
  obtain ⟨a, b, ha, hb, hab⟩ := P3FactorSegreEvaluation.exists_factors e f ρ hn
  exact ⟨i, hi, a, b, ha, hb, hab.trans (funext hcoeff)⟩

theorem polynomial_factors (e f : ℕ) (w : Index (e + f) → F) (hw : w ≠ 0)
    (himage : IntegerCoefficientProjectivePoint.point w hw ∈
      Set.range (P3FactorMultiplicationMap.multiplication e f)) :
    ∃ A B : MvPolynomial (Fin 4) F,
      A.IsHomogeneous e ∧ B.IsHomogeneous f ∧ A ≠ 0 ∧ B ≠ 0 ∧
        polynomial (e + f) w = A * B := by
  obtain ⟨i, hi, a, b, ha, hb, hab⟩ := normalized_factors e f w hw himage
  have he : polynomial (e + f) (fun m ↦ w m / w i) = polynomial e a * polynomial f b := by
    rw [← hab]
    exact (P3CoefficientMultiplication.reconstruct_tensor e f
      (P3FactorSegreFieldPoint.tensorVector e f a b)).trans
        (P3CoefficientMultiplication.pure_tensor_product e f a b)
  have hscale : C (w i) * polynomial (e + f) (fun m ↦ w m / w i) = polynomial (e + f) w := by
    have hc (m : Index (e + f)) : w i * (w m / w i) = w m := by
      rw [mul_comm, div_mul_cancel₀ _ hi]
    simp only [polynomial, Finset.mul_sum, C_mul_monomial, hc]
  refine ⟨C (w i) * polynomial e a, polynomial f b, ?_, homogeneous f b,
    mul_ne_zero (C_ne_zero.mpr hi) (nonzero e a ha), nonzero f b hb, ?_⟩
  · simpa only [zero_add] using (isHomogeneous_C (Fin 4) (w i)).mul (homogeneous e a)
  · rw [← hscale, he, mul_assoc]

omit [IsAlgClosed F] in
theorem positive_homogeneous_not_unit (P : MvPolynomial (Fin 4) F) {d : ℕ}
    (hd : 0 < d) (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) : ¬ IsUnit P := by
  intro hu
  have he := hP.totalDegree hP0
  have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
  omega

theorem not_irreducible (e f : ℕ) (he : 0 < e) (hf : 0 < f)
    (w : Index (e + f) → F) (hw : w ≠ 0)
    (himage : IntegerCoefficientProjectivePoint.point w hw ∈
      Set.range (P3FactorMultiplicationMap.multiplication e f)) :
    ¬ Irreducible (polynomial (e + f) w) := by
  obtain ⟨A, B, hA, hB, hA0, hB0, hAB⟩ := polynomial_factors e f w hw himage
  intro hirr
  exact (hirr.isUnit_or_isUnit hAB).elim
    (positive_homogeneous_not_unit A he hA hA0) (positive_homogeneous_not_unit B hf hB hB0)

end PaperP1.P3FactorImageFactorization
