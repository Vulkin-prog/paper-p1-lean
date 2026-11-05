module

public import PaperP1.Arithmetic.NormalizedCurveProjectionCount
public import PaperP1.Geometry.FiniteCurvePrimitiveCoordinate
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.FieldTheory.Perfect

/-! # The actual finite normalization supplies its canonical fraction fields and a bounded primitive counting projection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteNormalizationIntegerCount

universe u

open MvPolynomial IntegerCurveProjectionCoordinates QuadraticDegreeUniformFieldCount
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_primitive_count {F : Type u} [Field F] [CharZero F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
    [IsScalarTower F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (u₀ : Fin n → ℕ)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) =
      (aeval (R := F) (parameters I z u₀)).toRingHom)
    (hfinite : (aeval (R := F) (parameters I z u₀)).Finite)
    (hinj : Function.Injective (aeval (R := F) (parameters I z u₀)))
    (hrank : Module.finrank (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) = d)
    (hu : ∀ i, u₀ i ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1)) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1)) ∧
      ∀ (H : ℕ), 1 ≤ H → ∀ (S : Finset (Fin n → ℤ)),
        (∀ w ∈ S, w z = 1) →
        (∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0) →
        (∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) →
        (S.card : ℝ) ≤ (QuadraticAllDegreePlaneCount.constant.{u} + 1) *
          profile d (n * (((n - 1) * d ^ 2 + 1) ^ (n - 1)) * H) := by
  let R := MvPolynomial (Fin 2) F
  let A := MvPolynomial (Fin n) F ⧸ I
  let K := FractionRing R
  let L := FractionRing A
  let : Algebra R L := inferInstance
  let : IsScalarTower R A L := inferInstance
  let : Algebra F L := inferInstance
  let : IsScalarTower F A L := inferInstance
  let : Algebra F K := inferInstance
  let : IsScalarTower F R K := inferInstance
  have hmapinj : Function.Injective (algebraMap R A) := by rw [hsource]; exact hinj
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hmapinj
  let : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr ((IsFractionRing.injective A L).comp hmapinj)
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let : IsScalarTower F R L := IsScalarTower.to₁₂₄ F R A L
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq (fun r ↦ by
    rw [IsScalarTower.algebraMap_apply F R K, ← IsScalarTower.algebraMap_apply R K L]
    exact IsScalarTower.algebraMap_apply F R L r)
  let : CharZero K := Algebra.charZero_of_charZero F K
  have hdegree : Module.finrank K L = d := (IsFractionRing.finrank_eq R K A L).trans hrank
  let : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdegree]; exact hd)
  let : Algebra.IsSeparable K L := inferInstance
  let x : Fin n → A := fun i ↦ Ideal.Quotient.mk I (X i)
  obtain ⟨v, hv, hprimitive, _hmin, _hheight⟩ := FiniteCurvePrimitiveCoordinate.exists_coordinate
    (F := F) (R := R) (A := A) (K := K) (L := L) d hd hrank n x
    (CoordinateFractionFieldGenerators.quotient_variables_generate I)
  have heval : aeval (R := F) x = Ideal.Quotient.mkₐ F I := by
    apply MvPolynomial.algHom_ext
    intro i
    exact aeval_X _ i
  have hprim : IntermediateField.adjoin K {algebraMap A L (primitive I v)} = ⊤ := by
    rwa [heval] at hprimitive
  refine ⟨v, hv, ?_⟩
  intro H hH S hnormal hcurve hheight
  have hn : 1 ≤ n := by have := z.isLt; omega
  have hB : 1 ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1) := one_le_pow₀ (by omega)
  have hN : 1 ≤ n * (((n - 1) * d ^ 2 + 1) ^ (n - 1)) * H := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hn hB) hH
  exact NormalizedCurveProjectionCount.population_bound I hI d hd b₀ hp z u₀ v hsource hfinite hinj hrank
    hprim _ H hu hv hN S hnormal hcurve hheight

end PaperP1.FiniteNormalizationIntegerCount
