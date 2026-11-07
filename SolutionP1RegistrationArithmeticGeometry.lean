module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.NormNum
public import PaperP1.Analysis.QuadraticComparisonRange
public import PaperP1.Arithmetic.IntegralAffineCurvePointCount
public import PaperP1.Arithmetic.SplitProductBound
public import PaperP1.Asymptotics.ActualQuadraticComparisonCounterexample
public import PaperP1.Asymptotics.QuadraticGrowingDegreePlaneCount
public import PaperP1.Diophantine.UniformQuadraticCount
public import PaperP1.Model.RelativeSignIndependence

/-! # Arithmetic and geometry

Consolidated components retain their literal models, complete hypotheses and
original proof bodies, relocated into distinct model namespaces. The declaration
map records every original statement and source hash. No mathematical change.
-/

set_option autoImplicit false
@[expose] public noncomputable section

section ComponentQuadraticKernels

/-! # Prescribed squarefree kernels of shifted split products

These statements retain the actual integer and kernel bins, a positive
prescribed divisor, and the quantifier order of companion T5.1. The trivial
exponent cap repairs the original exact comparison. The uncapped counting
bound remains valid; its exact comparison is qualified, and the failure of
the unqualified display is witnessed on actual arbitrarily large data.
The Challenge uses only Mathlib. Its selected statement holes are not proof
evidence; the separate Solution supplies complete proofs.
-/

namespace PaperP1Registry.RegistrationModels.ArithmeticGeometry.QuadraticKernels
open Finset
open scoped Classical

/-- Prime exponents reduced modulo two. -/
def oddFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e : ℕ ↦ e % 2) (by simp)

/-- The ordinary squarefree kernel: the product of primes of odd valuation.
It is one on squares. The totalized value at zero is unused at positive scale. -/
def squarefreeKernel (n : ℕ) : ℕ := (oddFactorization n).support.prod id

/-- The squarefree kernel of the actual shifted split product. -/
def kernel (h n : ℕ) : ℕ := squarefreeKernel (n*(n+h))

/-- The literal integer and kernel bins, with the prescribed divisor. -/
def values (N h e : ℕ) (β : ℝ) : Finset ℕ :=
  (Icc N (2*N)).filter fun n ↦ (N : ℝ)^β ≤ kernel h n ∧
    (kernel h n : ℝ) < 2*(N : ℝ)^β ∧ e ∣ kernel h n

/-- The minimum of the two arithmetic counting exponents. -/
def rawExponent (β δ : ℝ) : ℝ := min (β-δ) (max (β/2-δ) (1-β/2))

/-- The additional trivial O(N) cap, needed for a universal exact comparison. -/
def cappedExponent (β δ : ℝ) : ℝ := min 1 (rawExponent β δ)

/-- The affine exponent in the corrected prescribed-kernel lemma. -/
def affineExponent (β δ : ℝ) : ℝ := 1/2+β/4-δ/2

/-- All three actual counting bounds for positive polylogarithmic shifts and
positive prescribed divisors. One threshold precedes every shift, divisor and
real kernel exponent. An arbitrary fixed positive power margin is explicit. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.quadratic_kernels_uniform_count (D A ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ,
      0 < h → 0 < e → (h : ℝ) ≤ D*(Real.log (N : ℝ))^A →
      ((values N h e β).card : ℝ) ≤
        (N : ℝ)^(rawExponent β (Real.log (e : ℝ)/Real.log (N : ℝ))+ε) ∧
      ((values N h e β).card : ℝ) ≤
        (N : ℝ)^(cappedExponent β (Real.log (e : ℝ)/Real.log (N : ℝ))+ε) ∧
      ((values N h e β).card : ℝ) ≤
        (N : ℝ)^(affineExponent β (Real.log (e : ℝ)/Real.log (N : ℝ))+ε) :=
by
  have hValues (N h e : ℕ) (β : ℝ) : values N h e β =
      PaperP1.PrescribedQuadraticKernelTheorem.values N h e β := by
    ext n
    simp [values, kernel, squarefreeKernel, oddFactorization,
      PaperP1.PrescribedQuadraticKernelTheorem.values, PaperP1.QuadraticKernelFibres.kernel,
      PaperP1.SmallPrimeBudget.squarefreeKernel, PaperP1.DefectivePredicate.oddPrimeSupport,
      PaperP1.DefectivePredicate.oddFactorization]
  obtain ⟨N₀,h₀⟩ := PaperP1.PrescribedQuadraticKernelTheorem.actual_exponent_counts D A ε hε
  refine ⟨max 2 N₀,le_max_left _ _,?_⟩
  intro N hN h e β hh he hShift
  simpa only [hValues, rawExponent, cappedExponent, affineExponent,
    PaperP1.QuadraticKernelExponents.exponent, PaperP1.QuadraticKernelExponents.capped,
    PaperP1.QuadraticKernelExponents.affine] using h₀ N (by omega) h e β hh he hShift

/-- The capped exact affine comparison holds for every pair of real parameters. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.quadratic_kernels_capped_comparison (β δ : ℝ) : cappedExponent β δ ≤ affineExponent β δ :=
by
  simpa only [rawExponent,cappedExponent,affineExponent,
    PaperP1.QuadraticKernelExponents.exponent,PaperP1.QuadraticKernelExponents.capped,
    PaperP1.QuadraticKernelExponents.affine] using
    PaperP1.QuadraticKernelExponents.capped_le_affine β δ

/-- With nonnegative divisor exponent, the uncapped exact comparison has this
necessary and sufficient range. Actual positive divisors at N>=2 satisfy the
sign condition. Without it this range is sufficient but need not be necessary. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.quadratic_kernels_uncapped_comparison_iff (β δ : ℝ) (hδ : 0 ≤ δ) :
    rawExponent β δ ≤ affineExponent β δ ↔ β-2*δ ≤ 2 :=
by
  simpa only [rawExponent,affineExponent,
    PaperP1.QuadraticKernelExponents.exponent,PaperP1.QuadraticKernelExponents.affine] using
    PaperP1.QuadraticComparisonRange.exponent_le_affine_iff_of_nonneg_delta β δ hδ

/-- The exact kernel exponent of N(N+1) at scale N. -/
def adjacentExponent (N : ℕ) : ℝ := Real.log ((N : ℝ)*((N : ℝ)+1))/Real.log (N : ℝ)

/-- The uncapped comparison in the original display fails on arbitrarily large
actual admissible data h=e=1, n=N, with consecutive squarefree N and N+1.
This refutes only the unrestricted exact comparison; all counting bounds above
remain valid. The shift obeys every nonnegative logarithmic power budget. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.quadratic_kernels_actual_uncapped_counterexamples (M : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ N : ℕ, M < N ∧ 2 ≤ N ∧ Squarefree N ∧ Squarefree (N+1) ∧
      (1 : ℝ) ≤ (Real.log (N : ℝ))^A ∧
      N ∈ values N 1 1 (adjacentExponent N) ∧ 2 < adjacentExponent N ∧
      affineExponent (adjacentExponent N) 0 < rawExponent (adjacentExponent N) 0 :=
by
  have hValues (N h e : ℕ) (β : ℝ) : values N h e β =
      PaperP1.PrescribedQuadraticKernelTheorem.values N h e β := by
    ext n
    simp [values, kernel, squarefreeKernel, oddFactorization,
      PaperP1.PrescribedQuadraticKernelTheorem.values, PaperP1.QuadraticKernelFibres.kernel,
      PaperP1.SmallPrimeBudget.squarefreeKernel, PaperP1.DefectivePredicate.oddPrimeSupport,
      PaperP1.DefectivePredicate.oddFactorization]
  obtain ⟨Nlog,hLog⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually 1
  obtain ⟨N,hN,hSf,hNext⟩ := PaperP1.AdjacentSquarefreeCount.arbitrarily_large (max M (max 2 Nlog))
  have hN2 : 2 ≤ N := by omega
  refine ⟨N,by omega,hN2,hSf,hNext,
    Real.one_le_rpow (hLog N (by omega)).1 hA,?_,?_,?_⟩
  · rw [hValues]
    simpa only [adjacentExponent,PaperP1.ActualQuadraticComparisonCounterexample.beta] using
      PaperP1.ActualQuadraticComparisonCounterexample.source_value N hN2 hSf hNext
  · simpa only [adjacentExponent,PaperP1.ActualQuadraticComparisonCounterexample.beta] using
      PaperP1.ActualQuadraticComparisonCounterexample.beta_gt_two N hN2
  · simpa only [adjacentExponent,rawExponent,affineExponent,
      PaperP1.ActualQuadraticComparisonCounterexample.beta,
      PaperP1.QuadraticKernelExponents.exponent,PaperP1.QuadraticKernelExponents.affine] using
      PaperP1.ActualQuadraticComparisonCounterexample.comparison_failure N hN2

end PaperP1Registry.RegistrationModels.ArithmeticGeometry.QuadraticKernels

end ComponentQuadraticKernels

section ComponentIntegralCurveCount

/-! # Degree-uniform integer points on integral curves
Actual integer grids are defined by polynomial evaluation. Curve degree and
dimension are expressed through the literal homogeneous quotient pieces and
their eventual linear Hilbert function. No point-count estimate is assumed.
The constants precede every curve, coefficient field, degree and height.
-/

namespace PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount
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


theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount.quotientPiece_eq_source {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (r : ℕ) :
    quotientPiece I r=PaperP1.HomogeneousQuotientGrading.piece
      (MvPolynomial.homogeneousSubmodule σ F) I r := rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount.linearHilbert_iff_source {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F)) (d : ℕ) (b : ℚ) :
    LinearHilbert I d b ↔ PaperP1.GradedHilbertPolynomial.IsHilbertPolynomial
      (PaperP1.HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule σ F) I)
      (Polynomial.C (d : ℚ)*Polynomial.X+Polynomial.C b) := by
  simp only [LinearHilbert,quotientPiece_eq_source,
    PaperP1.GradedHilbertPolynomial.IsHilbertPolynomial,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount.affinePoints_eq_source {F : Type*} [Field F] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n+1)) F)) (N : ℕ) :
    affinePoints n I N=PaperP1.IntegralAffineCurvePointCount.points n I N := rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount.planeDegree_eq_source {F : Type*} [Semiring F] (P : F[X][X]) :
    planeDegree P=PaperP1.PlaneCurvePointCount.degree P := rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount.planeGrid_eq_source {F : Type*} [Ring F] (P : F[X][X]) (N : ℕ) :
    planeGrid P N=PaperP1.PlaneCurvePointCount.grid P N := rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount.upperPowerCap_iff_source (a : ℝ) (cap : ℕ → ℝ) :
    UpperPowerCap a cap ↔ PaperP1.PlaneCurvePointCount.UpperPowerCap a cap := Iff.rfl

/-- Full dimension-uniform quadratic degree estimate, with logarithmic power 17.
The bound holds over every characteristic-zero field, without a chosen embedding. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.integral_curve_count_all_dimensional_count : ∀ n : ℕ, ∃ c : ℝ, 0<c ∧
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
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.integral_curve_count_plane_count : ∃ c : ℝ, 0<c ∧
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
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.integral_curve_count_growing_degree_sublinear (c₀ a : ℝ) (hc₀ : 0<c₀) (ha : 0≤a) (ha₁ : a<1/2)
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

end PaperP1Registry.RegistrationModels.ArithmeticGeometry.IntegralCurveCount

end ComponentIntegralCurveCount

section ComponentLocalRigidity

/-! # Uniform local arithmetic rigidity
The split-product and quadratic counts retain the degree and coefficient
uniformity of companion T1.1 and T1.2. The actual even square-relation
code, Griesmer budget, logarithmic ranks and independent relative prime
signs spell out main lemma 2.1. Prime-sign and Pell foundations are
adapted through P1 from Paper C commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0.
Five selected Challenge holes are deliberate statement placeholders.
-/

namespace PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity
open Finset MeasureTheory
open scoped Classical ENNReal

/-- Prime signs are represented by bits: zero means +1 and one means -1. -/
abbrev F₂ := ZMod 2
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance measurableF₂ : MeasurableSpace F₂ := ⊤
abbrev Sample := ℕ → F₂

/-- A fair prime-sign bit, with its discrete sigma algebra. -/
def coordinateMeasure : Measure F₂ := Measure.uniformOfFinset (univ : Finset F₂)

instance coordinateProbability : IsProbabilityMeasure coordinateMeasure := by
  constructor
  rw [coordinateMeasure,Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- Independent fair bits, indexed in increasing prime order. -/
def primeSignMeasure : Measure Sample := Measure.infinitePi (fun _ : ℕ ↦ coordinateMeasure)

instance primeSignProbability : IsProbabilityMeasure primeSignMeasure := by
  unfold primeSignMeasure
  infer_instance

/-- Exponent parities of an integer's prime factorization. -/
def parity (n : ℕ) : ℕ →₀ F₂ := n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)

/-- The actual completely multiplicative value, represented as a sign bit.
Prime p uses its coordinate primeCounting' p. -/
def valueBit (ω : Sample) (n : ℕ) : F₂ :=
  (parity n).sum fun p e ↦ ω (Nat.primeCounting' p)*e

/-- Every even square relation in the literal B-vertex window. -/
def windowParityMap (U B : ℕ) : (Fin B → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun i ↦ parity (U+i.val))

def windowEvennessMap (B : ℕ) : (Fin B → F₂) →ₗ[F₂] F₂ :=
  Fintype.linearCombination F₂ (fun _ ↦ 1)

def relationCode (U B : ℕ) : Submodule F₂ (Fin B → F₂) :=
  LinearMap.ker (windowParityMap U B) ⊓ LinearMap.ker (windowEvennessMap B)

def relationRank (U B : ℕ) : ℕ := Module.finrank F₂ (relationCode U B)

def distance (U B : ℕ) : ℕ := ⌈Real.log U/Real.log (64*(B : ℝ))⌉₊

/-- Positive integer solutions of the literal equation, including both height endpoints. -/
def positiveSolutions (a b : ℕ) (h : ℤ) (H : ℕ) : Finset (ℤ×ℤ) :=
  ((Icc 1 (H : ℤ)) ×ˢ Icc 1 (H : ℤ)).filter fun z ↦
    (a : ℤ)*z.1^2-(b : ℤ)*z.2^2=h

def randomValue (ω : Sample) (n : ℕ) : ℤ := if valueBit ω n=0 then 1 else -1

/-- The reference vertex is U+1; all the other B-1 vertices occur exactly once. -/
def relativeVertex (U B : ℕ) (i : Fin (B-1)) : ℕ :=
  if i.val=0 then U else U+1+i.val

def relativeSign (U B : ℕ) (i : Fin (B-1)) (ω : Sample) : ℤ :=
  randomValue ω (relativeVertex U B i)*randomValue ω (U+1)

def relativeBits (U B : ℕ) (ω : Sample) (i : Fin (B-1)) : F₂ :=
  if i.val=0 then valueBit ω U+valueBit ω (U+1)
  else valueBit ω (U+1)+valueBit ω (U+1+i.val)

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.parity_eq (n : ℕ) : parity n=PaperP1.Arithmetic.parityVec n := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.relationCode_eq (U B : ℕ) : relationCode U B=
    PaperP1.WindowRelationCode.windowRelationCode U B := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.relationRank_eq (U B : ℕ) : relationRank U B=
    Module.finrank F₂ (PaperP1.WindowRelationCode.windowRelationCode U B) := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.distance_eq (U B : ℕ) : distance U B=PaperP1.LocalRigidityCode.rungeDistance U B := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.positiveSolutions_eq (a b : ℕ) (h : ℤ) (H : ℕ) : positiveSolutions a b h H=
    PaperP1.UniformQuadraticCount.positiveQuadraticSolutions a b h H := by
  ext z
  simp only [positiveSolutions,PaperP1.UniformQuadraticCount.positiveQuadraticSolutions,
    Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,PaperP1.PellInput.pellEquation]

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.relativeBits_eq (U B : ℕ) : relativeBits U B=
    PaperP1.RelativeSignIndependence.infiniteStartBits (U+1) (B-1) := by
  funext ω i
  simp only [relativeBits,PaperP1.RelativeSignIndependence.infiniteStartBits,Nat.add_sub_cancel]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.relativeSign_eq (U B : ℕ) : relativeSign U B=
    PaperP1.RelativeSignIndependence.relativeSign (U+1) (B-1) := by
  funext i ω
  simp only [relativeSign,relativeVertex,randomValue,
    PaperP1.RelativeSignIndependence.relativeSign,PaperP1.RelativeSignIndependence.relativeVertex,
    PaperP1.Model.InfiniteRademacher.infiniteRandomValue,PaperP1.Model.phase,Nat.add_sub_cancel]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity.primeSignMeasure_eq : primeSignMeasure=
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure := by rfl

/-- Uniform in every even degree, with the original constant 64. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_split_product_bound {k : ℕ} (hk : 1≤k) {R : ℝ} (hR : 1≤R)
    {U : ℤ} (hU : 2*R≤(U : ℝ)) (γ : Fin (2*k) → ℤ)
    (hγ : ∀ i, |(γ i : ℝ)|≤R) (hinj : Function.Injective γ)
    (a : ℤ) (hsquare : ∏ i, (U+γ i)=a^2) :
    (U : ℝ)≤(64*R)^(2*k) := by
  exact PaperP1.SplitProductBound.uniform_split_product_real_radius hk hR hU γ hγ hinj a hsquare

/-- One cutoff precedes all coefficients, nonzero signs and positive solutions. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_uniform_quadratic_count (A₀ : ℝ) (hA₀ : 0<A₀) (ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (a b : ℕ) (h : ℤ),
      0<a → 0<b → h≠0 → (a : ℝ)≤(N : ℝ)^A₀ → (b : ℝ)≤(N : ℝ)^A₀ →
      |(h : ℝ)|≤(N : ℝ)^A₀ →
      ((positiveSolutions a b h ⌊(N : ℝ)^A₀⌋₊).card : ℝ)≤(N : ℝ)^ε := by
  simpa only [positiveSolutions_eq] using
    PaperP1.UniformQuadraticCount.uniform_quadratic_equation_count A₀ hA₀ ε hε

/-- The real, untruncated Griesmer sum for the actual even square-relation code. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_finite_relative_griesmer {U B t : ℕ} (hB : 1≤B) (hU : 2*B≤U)
    (ht : t≤relationRank U B) :
    (∑ i ∈ range t, (⌈(distance U B : ℝ)/(2 : ℝ)^i⌉₊ : ℝ))-(t : ℝ)≤
      (Nat.primeCounting B : ℝ)+1 := by
  have h := PaperP1.WindowRelationCode.window_relation_griesmer_real hB hU
    (by simpa only [relationRank_eq] using ht)
  simpa only [distance_eq,PaperP1.LocalRigidityCode.primeCount_eq_primeCounting] using h

/-- Both exact original logarithmic regimes, with every base after the threshold. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_logarithmic_rank_regimes (a : ℝ) (ha : 0<a) :
    (∀ B : ℕ → ℕ,
      Asymptotics.IsLittleO Filter.atTop
        (fun N ↦ (B N : ℝ)-Real.log N/Real.log 2) (fun N ↦ Real.log (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : ℕ, a*N≤(U : ℝ) → relationRank U (B N)≤1) ∧
    (∀ c : ℝ, 0<c → ∀ t : ℕ, c<2-(2 : ℝ)^(1-(t : ℤ)) → ∀ B : ℕ → ℕ,
      Asymptotics.IsEquivalent Filter.atTop (fun N ↦ (B N : ℝ))
        (fun N ↦ c*Real.log (N : ℝ)) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U : ℕ, a*N≤(U : ℝ) → relationRank U (B N)<t) := by
  constructor
  · intro B hB
    simpa only [relationRank_eq] using
      PaperP1.LocalRigidityRegimes.critical_relation_rank_le_one_of_error a ha B hB
  · intro c hc t hct B hB
    simpa only [relationRank_eq] using
      PaperP1.LocalRigidityRegimes.relation_rank_lt_of_length_asymptotic a c ha hc t hct B hB

/-- Actual fair product law of all relative bits, and exact independence of the signs. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_subcritical_relative_signs (a ε : ℝ) (ha : 0<a) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U B : ℕ, 1≤B → a*N≤(U : ℝ) →
      (B : ℝ)≤(1-ε)*Real.log N →
      primeSignMeasure.map (relativeBits U B)=
        Measure.pi (fun _ : Fin (B-1) ↦ coordinateMeasure) ∧
      ProbabilityTheory.iIndepFun (relativeSign U B) primeSignMeasure := by
  obtain ⟨N₀,hN₀⟩ := PaperP1.UniformLocalRigidity.uniform_subcritical_relation_rank_zero a ε ha hε
  refine ⟨N₀, fun N hN U B hB hbase hwidth ↦ ?_⟩
  have hrel : Module.finrank F₂
      (PaperP1.WindowRelationCode.windowRelationCode (U+1-1) (B-1+1))=0 := by
    rw [Nat.add_sub_cancel,Nat.sub_add_cancel hB]
    exact hN₀ N hN U B hbase hwidth
  constructor
  · rw [relativeBits_eq,primeSignMeasure_eq]
    exact PaperP1.RelativeSignIndependence.map_infiniteStartBits_eq_pi (by omega : 0<U+1) hrel
  · rw [relativeSign_eq,primeSignMeasure_eq]
    exact PaperP1.RelativeSignIndependence.iIndepFun_relativeSigns (by omega : 0<U+1) hrel
end PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity

end ComponentLocalRigidity
