module

public import PaperP1.Geometry.IntegerCurveProjectionCount
public import PaperP1.Arithmetic.QuadraticAllDegreePlaneCount

/-! # The actual normalized source population obeys the proved plane profile at its actual projected height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedCurveProjectionCount

universe u

open MvPolynomial IntegerCurveProjectionCoordinates QuadraticDegreeUniformFieldCount
attribute [local instance] MvPolynomial.gradedAlgebra

theorem population_bound {F : Type u} [Field F] [CharZero F] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
    [IsScalarTower F (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I)]
    {K L : Type*} [Field K] [Field L]
    [Algebra (MvPolynomial (Fin 2) F) K] [Algebra K L]
    [Algebra (MvPolynomial (Fin n) F ⧸ I) L] [Algebra (MvPolynomial (Fin 2) F) L]
    [IsScalarTower (MvPolynomial (Fin 2) F) K L]
    [IsScalarTower (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) L]
    [IsFractionRing (MvPolynomial (Fin 2) F) K] [IsFractionRing (MvPolynomial (Fin n) F ⧸ I) L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin n) F))
    (d : ℕ) (hd : 0 < d) (b₀ : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin n) F) I)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b₀))
    (z : Fin n) (u v : Fin n → ℕ)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) =
      (aeval (R := F) (parameters I z u)).toRingHom)
    (hfinite : (aeval (R := F) (parameters I z u)).Finite)
    (hinj : Function.Injective (aeval (R := F) (parameters I z u)))
    (hrank : Module.finrank (MvPolynomial (Fin 2) F) (MvPolynomial (Fin n) F ⧸ I) = d)
    (hprimitive : IntermediateField.adjoin K
      {algebraMap (MvPolynomial (Fin n) F ⧸ I) L (primitive I v)} = ⊤)
    (B H : ℕ) (hu : ∀ i, u i ≤ B) (hv : ∀ i, v i ≤ B) (hN : 1 ≤ n * B * H)
    (S : Finset (Fin n → ℤ)) (hnormal : ∀ w ∈ S, w z = 1)
    (hcurve : ∀ w ∈ S, ∀ P ∈ I, eval (fun i ↦ (w i : F)) P = 0)
    (hheight : ∀ w ∈ S, ∀ i, (w i).natAbs ≤ H) :
    (S.card : ℝ) ≤ (QuadraticAllDegreePlaneCount.constant.{u} + 1) * profile d (n * B * H) := by
  obtain ⟨hP, hdegree, hc⟩ := IntegerCurveProjectionCount.population I hI d hd b₀ hp z u v
    hsource hfinite hinj hrank hprimitive B H hu hv S hnormal hcurve hheight
  have hgrid := QuadraticAllDegreePlaneCount.grid_le d (n * B * H) hd hN F
    (LinearPlaneImageAffineEquation.equation (F := F) (primitive I v)) hdegree hP
  have hcast : (S.card : ℝ) ≤
      ((PlaneCurvePointCount.grid (LinearPlaneImageAffineEquation.equation (F := F) (primitive I v))
        (n * B * H)).card : ℝ) + (((d - 1) * d : ℕ) : ℝ) := by
    exact_mod_cast hc
  have he : (((d - 1) * d : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast (show (d - 1) * d ≤ d ^ 2 by nlinarith [Nat.sub_le d 1])
  have hsection := he.trans (degree_square_le_profile d (n * B * H) hN)
  calc
    _ ≤ QuadraticAllDegreePlaneCount.constant * profile d (n * B * H) + profile d (n * B * H) :=
      hcast.trans (add_le_add hgrid hsection)
    _ = _ := by ring

end PaperP1.NormalizedCurveProjectionCount
