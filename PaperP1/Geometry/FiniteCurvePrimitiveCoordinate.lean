module

public import PaperP1.Algebra.CoordinateFractionFieldGenerators
public import PaperP1.Arithmetic.IntegerLinearFormHeight
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # An actual degree-D finite normalization gives a bounded primitive original linear coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCurvePrimitiveCoordinate

theorem exists_coordinate {F R A K L : Type*} [Field F] [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [Field K] [CharZero K] [Field L]
    [Algebra F A] [Algebra F K] [Algebra F L] [Algebra R A] [Algebra R K]
    [Algebra A L] [Algebra R L] [Algebra K L]
    [IsScalarTower F A L] [IsScalarTower F K L] [IsScalarTower R A L] [IsScalarTower R K L]
    [IsFractionRing R K] [IsFractionRing A L]
    (d : ℕ) (hd : 0 < d) (hrank : Module.finrank R A = d)
    (n : ℕ) (x : Fin n → A) (hgen : Algebra.adjoin F (Set.range x) = ⊤) :
    ∃ u : Fin n → ℕ, (∀ i, u i ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1)) ∧
      (IntermediateField.adjoin K
        {algebraMap A L (MvPolynomial.aeval x
          (CommonLinearNormalization.form (fun i ↦ (u i : F))))} = ⊤) ∧
      ((minpoly K (algebraMap A L (MvPolynomial.aeval x
        (CommonLinearNormalization.form (fun i ↦ (u i : F)))))).natDegree = d) ∧
      ∀ (H : ℕ) (v : Fin n → ℤ), (∀ i, (v i).natAbs ≤ H) →
        |MvPolynomial.eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤
          ((n * (((n - 1) * d ^ 2 + 1) ^ (n - 1)) * H : ℕ) : ℤ) := by
  have hdegree : Module.finrank K L = d := (IsFractionRing.finrank_eq R K A L).trans hrank
  let : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hdegree]; exact hd)
  obtain ⟨u, hu, hprimitive, hmin⟩ := CoordinateFractionFieldGenerators.bounded_primitive
    (F := F) (A := A) (K := K) (L := L) n x hgen
  have huD : ∀ i, u i ≤ ((n - 1) * d ^ 2 + 1) ^ (n - 1) := by
    simpa only [hdegree] using hu
  refine ⟨u, huD, hprimitive, ?_, ?_⟩
  · exact hmin.trans hdegree
  · intro H v hv
    exact IntegerLinearFormHeight.evaluation_bound n _ H u huD v hv

end PaperP1.FiniteCurvePrimitiveCoordinate
