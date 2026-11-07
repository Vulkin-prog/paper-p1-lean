module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.InnerProductSpace.Basic
public import PaperP1.Arithmetic.IntegralAffineCurvePointCount
public import PaperP1.Asymptotics.QuadraticGrowingDegreePlaneCount

/-! # Degree-uniform integer points on integral curves
Actual integer grids are defined by polynomial evaluation. Curve degree and
dimension are expressed through the literal homogeneous quotient pieces and
their eventual linear Hilbert function. No point-count estimate is assumed.
The constants precede every curve, coefficient field, degree and height.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1Registry.IntegralCurveCount
universe u
open Finset Polynomial MvPolynomial
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal degree-r homogeneous piece of the quotient coordinate ring. -/
def quotientPiece {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) (r : ℕ) :
    Submodule F (MvPolynomial σ F ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ F r).map (Ideal.Quotient.mkₐ F I).toLinearMap

/-- Eventual linear Hilbert function, with positive slope supplied separately. -/
def LinearHilbert {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F))
    (d : ℕ) (b : ℚ) : Prop :=
  ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
    (d : ℚ)*(r : ℚ)+b=(Module.finrank F (quotientPiece I r) : ℚ)

/-- The exact integer box, including both endpoints. -/
def integerBox (N : ℕ) : Finset ℤ := Icc (-(N : ℤ)) N

/-- Every affine integer point, in the chart with initial coordinate one. -/
def affinePoints {F : Type*} [Field F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n+1)) F)) (N : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset (fun _ : Fin n ↦ integerBox N)).filter fun w ↦
    ∀ P ∈ I, MvPolynomial.eval (Fin.cons (1 : F) (fun i ↦ (w i : F))) P=0

/-- Total degree of a literal bivariate polynomial. -/
def planeDegree {F : Type*} [Semiring F] (P : F[X][X]) : ℕ :=
  P.support.sup fun y ↦ y+(P.coeff y).natDegree

def planeGrid {F : Type*} [Ring F] (P : F[X][X]) (N : ℕ) : Finset (ℤ×ℤ) :=
  ((integerBox N) ×ˢ (integerBox N)).filter fun p ↦
    P.evalEval (p.1 : F) (p.2 : F)=0

/-- Only an upper growth cap is required; no lower asymptotic for the cap. -/
def UpperPowerCap (a : ℝ) (cap : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0<δ → ∃ B₀ : ℕ, ∀ B ≥ B₀, cap B ≤ (B : ℝ)^(a+δ)


theorem quotientPiece_eq_source {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (r : ℕ) :
    quotientPiece I r=PaperP1.HomogeneousQuotientGrading.piece
      (MvPolynomial.homogeneousSubmodule σ F) I r := rfl

theorem linearHilbert_iff_source {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (d : ℕ) (b : ℚ) :
    LinearHilbert I d b ↔ PaperP1.GradedHilbertPolynomial.IsHilbertPolynomial
      (PaperP1.HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ)*Polynomial.X+Polynomial.C b) := by
  simp only [LinearHilbert,quotientPiece_eq_source,
    PaperP1.GradedHilbertPolynomial.IsHilbertPolynomial,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  rfl

theorem affinePoints_eq_source {F : Type*} [Field F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n+1)) F)) (N : ℕ) :
    affinePoints n I N=PaperP1.IntegralAffineCurvePointCount.points n I N := rfl

theorem planeDegree_eq_source {F : Type*} [Semiring F] (P : F[X][X]) :
    planeDegree P=PaperP1.PlaneCurvePointCount.degree P := rfl

theorem planeGrid_eq_source {F : Type*} [Ring F] (P : F[X][X]) (N : ℕ) :
    planeGrid P N=PaperP1.PlaneCurvePointCount.grid P N := rfl

theorem upperPowerCap_iff_source (a : ℝ) (cap : ℕ → ℝ) :
    UpperPowerCap a cap ↔ PaperP1.PlaneCurvePointCount.UpperPowerCap a cap := Iff.rfl

/-- Full dimension-uniform quadratic degree estimate, with logarithmic power 17.
The bound holds over every characteristic-zero field, without a chosen embedding. -/
theorem all_dimensional_count : ∀ n : ℕ, ∃ c : ℝ, 0<c ∧
    ∀ (F : Type u) [Field F] [CharZero F],
    ∀ (I : Ideal (MvPolynomial (Fin (n+1)) F)),
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) F) → I.IsPrime →
      ∀ d : ℕ, 0<d → ∀ b : ℚ, LinearHilbert I d b →
      ∀ H : ℝ, 2<H → ((affinePoints n I ⌊H⌋₊).card : ℝ) ≤
        c*(d : ℝ)^2*H^(1/(d : ℝ))*Real.log H^(17 : ℝ) :=
by
  intro n
  refine ⟨PaperP1.UniformIntegralCurveCount.realConstant.{u} (n+1),
    PaperP1.UniformIntegralCurveCount.realConstant_pos (n+1),?_⟩
  intro F _hF _hchar I hI hprime d hd b hp H hH
  have hp' := (linearHilbert_iff_source I d b).mp hp
  have h := PaperP1.IntegralAffineCurvePointCount.grid_bound n I hI hprime d hd b hp' H hH
  rw [show (17 : ℝ)=((17 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
  simpa only [affinePoints_eq_source] using h

/-- One absolute coefficient- and degree-uniform constant for all plane curves.
Ordinary irreducibility over the stated field suffices. -/
theorem plane_count : ∃ c : ℝ, 0<c ∧
    ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X],
      Irreducible P → 0<planeDegree P → ∀ H : ℝ, 2<H →
      ((planeGrid P ⌊H⌋₊).card : ℝ) ≤
        c*(planeDegree P : ℝ)^2*H^(1/(planeDegree P : ℝ))*Real.log H^(17 : ℝ) :=
by
  obtain ⟨c,hc,h⟩ := PaperP1.QuadraticPlaneUniformBound.uniform_bound
  refine ⟨c,hc,?_⟩
  intro K _hK _hchar _halg P hP hD H hH
  have h' := h K P hP hD H hH
  simpa only [planeGrid_eq_source,planeDegree_eq_source,
    PaperP1.CurveDegreeProfile.profile,mul_assoc] using h'

/-- Complete quadratic endpoint budget and o(B) conclusion on the actual floor
box, uniformly over all curves below any stated upper power cap with a<1/2. -/
theorem growing_degree_sublinear (c₀ a : ℝ) (hc₀ : 0<c₀) (ha : 0≤a) (ha₁ : a<1/2)
    (cap : ℕ → ℝ) (hcap : UpperPowerCap a cap) :
    (∃ A : ℝ, 0<A ∧ ∃ B₀ : ℕ, 2≤B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X],
        Irreducible P → 2≤planeDegree P → (planeDegree P : ℝ)≤cap B →
        ((planeGrid P ⌊c₀*B⌋₊).card : ℝ) ≤
          A*((B : ℝ)^(1/2 : ℝ)+(cap B)^2)*Real.log B^(17 : ℝ)) ∧
    (∀ ε : ℝ, 0<ε → ∃ B₀ : ℕ, 2≤B₀ ∧ ∀ B ≥ B₀,
      ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X],
        Irreducible P → 2≤planeDegree P → (planeDegree P : ℝ)≤cap B →
        ((planeGrid P ⌊c₀*B⌋₊).card : ℝ) ≤ ε*B) :=
by
  exact PaperP1.QuadraticGrowingDegreePlaneCount.article_13_5 c₀ a hc₀ ha ha₁ cap hcap

end PaperP1Registry.IntegralCurveCount
