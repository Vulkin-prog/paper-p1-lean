module

public import PaperP1.Geometry.PresentedProjectiveCurveData
public import PaperP1.Geometry.ProjectiveCurveHilbertDegree
public import PaperP1.Arithmetic.FiniteIndexIntegralCurveCount
public import PaperP1.Arithmetic.NormalizedIntegerPoints

/-! # The actual degree-quadratic integer-point bound on every presented projective curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PresentedCurveQuadraticCount

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ B : Type} [Finite σ] [CommRing B] [Algebra ℚ B]
  {H : ℕ → Submodule ℚ B} [GradedAlgebra H]
  (f : MvPolynomial.homogeneousSubmodule σ ℚ →+*ᵍ H)
  (hscalar : ∀ a : ℚ, f (algebraMap ℚ (MvPolynomial σ ℚ) a) = algebraMap ℚ B a)
  (honto : Function.Surjective f) (Γ : GradedProjectiveCurveData.Curve H)

include hscalar honto

theorem population_bound (z : σ) (N : ℕ) (hN : 1 ≤ N) (S : Finset (σ → ℤ))
    (hnormal : ∀ v ∈ S, v z = 1)
    (hcurve : ∀ v ∈ S, ∀ P ∈ PresentedProjectiveCurveData.coordinateIdeal f Γ,
      MvPolynomial.eval (fun i ↦ (v i : ℚ)) P = 0)
    (hheight : ∀ v ∈ S, ∀ i, (v i).natAbs ≤ N) :
    (S.card : ℝ) ≤ UniformIntegralCurveCount.constant.{0} (Nat.card σ) *
      (Γ.degree : ℝ) ^ 2 * (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 *
        (N : ℝ) ^ (1 / (Γ.degree : ℝ)) := by
  let Δ := PresentedProjectiveCurveData.toCurve f hscalar honto Γ
  let d := ProjectiveCurveHilbertDegree.natDegree Δ
  have hd : 0 < d := ProjectiveCurveHilbertDegree.natDegree_pos Δ
  have hdQ : (d : ℚ) = Γ.degree := ProjectiveCurveHilbertDegree.natDegree_cast Δ
  have hdR : (d : ℝ) = (Γ.degree : ℝ) := by exact_mod_cast hdQ
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial
      (ProjectiveCurveData.piece (PresentedProjectiveCurveData.coordinateIdeal f Γ))
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C Γ.constant) := by
    rw [hdQ]
    exact PresentedProjectiveCurveData.coordinate_hilbert f hscalar honto Γ
  have hc := FiniteIndexIntegralCurveCount.population_bound
    (PresentedProjectiveCurveData.coordinateIdeal f Γ)
    (PresentedProjectiveCurveData.coordinateIdeal_homogeneous f Γ)
    (PresentedProjectiveCurveData.coordinateIdeal_prime f Γ) d hd Γ.constant hp z N hN S
    hnormal hcurve hheight
  unfold QuadraticDegreeUniformFieldCount.profile at hc
  rw [hdR] at hc
  simpa only [mul_assoc] using hc

theorem points_bound (z : σ) (N : ℕ) (hN : 1 ≤ N) :
    ((NormalizedIntegerPoints.points (PresentedProjectiveCurveData.coordinateIdeal f Γ) z N).card : ℝ) ≤
      UniformIntegralCurveCount.constant.{0} (Nat.card σ) *
        (Γ.degree : ℝ) ^ 2 * (DegreeUniformAffineParameters.logarithmicBudget N : ℝ) ^ 17 *
          (N : ℝ) ^ (1 / (Γ.degree : ℝ)) := by
  let S := NormalizedIntegerPoints.points (PresentedProjectiveCurveData.coordinateIdeal f Γ) z N
  have hnormal (v : σ → ℤ) (hv : v ∈ S) : v z = 1 :=
    ((NormalizedIntegerPoints.mem_points _ z N v).mp hv).1.2
  have hcurve (v : σ → ℤ) (hv : v ∈ S) :
      ∀ P ∈ PresentedProjectiveCurveData.coordinateIdeal f Γ,
        MvPolynomial.eval (fun i ↦ (v i : ℚ)) P = 0 :=
    ((NormalizedIntegerPoints.mem_points _ z N v).mp hv).2
  have hheight (v : σ → ℤ) (hv : v ∈ S) (i : σ) : (v i).natAbs ≤ N := by
    have hh := ((NormalizedIntegerPoints.mem_points _ z N v).mp hv).1.1 i
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  exact population_bound f hscalar honto Γ z N hN S hnormal hcurve hheight

end PaperP1.PresentedCurveQuadraticCount
