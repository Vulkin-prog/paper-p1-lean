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
by sorry

/-- The capped exact affine comparison holds for every pair of real parameters. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.quadratic_kernels_capped_comparison (β δ : ℝ) : cappedExponent β δ ≤ affineExponent β δ :=
by sorry

/-- With nonnegative divisor exponent, the uncapped exact comparison has this
necessary and sufficient range. Actual positive divisors at N>=2 satisfy the
sign condition. Without it this range is sufficient but need not be necessary. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.quadratic_kernels_uncapped_comparison_iff (β δ : ℝ) (hδ : 0 ≤ δ) :
    rawExponent β δ ≤ affineExponent β δ ↔ β-2*δ ≤ 2 :=
by sorry

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
by sorry

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

/-- Full dimension-uniform quadratic degree estimate, with logarithmic power 17.
The bound holds over every characteristic-zero field, without a chosen embedding. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.integral_curve_count_all_dimensional_count : ∀ n : ℕ, ∃ c : ℝ, 0<c ∧
    ∀ (F : Type u) [Field F] [CharZero F],
    ∀ (I : Ideal (MvPolynomial (Fin (n+1)) F)),
      I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (n+1)) F) → I.IsPrime →
      ∀ d : ℕ, 0<d → ∀ b : ℚ, LinearHilbert I d b →
      ∀ H : ℝ, 2<H → ((affinePoints n I ⌊H⌋₊).card : ℝ) ≤
        c*(d : ℝ)^2*H^(1/(d : ℝ))*Real.log H^(17 : ℝ) :=
by sorry

/-- One absolute coefficient- and degree-uniform constant for all plane curves.
Ordinary irreducibility over the stated field suffices. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.integral_curve_count_plane_count : ∃ c : ℝ, 0<c ∧
    ∀ (K : Type) [Field K] [CharZero K] [Algebra K ℂ], ∀ P : K[X][X],
      Irreducible P → 0<planeDegree P → ∀ H : ℝ, 2<H →
      ((planeGrid P ⌊H⌋₊).card : ℝ) ≤
        c*(planeDegree P : ℝ)^2*H^(1/(planeDegree P : ℝ))*Real.log H^(17 : ℝ) :=
by sorry

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
by sorry

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

/-- Uniform in every even degree, with the original constant 64. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_split_product_bound {k : ℕ} (hk : 1≤k) {R : ℝ} (hR : 1≤R)
    {U : ℤ} (hU : 2*R≤(U : ℝ)) (γ : Fin (2*k) → ℤ)
    (hγ : ∀ i, |(γ i : ℝ)|≤R) (hinj : Function.Injective γ)
    (a : ℤ) (hsquare : ∏ i, (U+γ i)=a^2) :
    (U : ℝ)≤(64*R)^(2*k) := by
  sorry

/-- One cutoff precedes all coefficients, nonzero signs and positive solutions. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_uniform_quadratic_count (A₀ : ℝ) (hA₀ : 0<A₀) (ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (a b : ℕ) (h : ℤ),
      0<a → 0<b → h≠0 → (a : ℝ)≤(N : ℝ)^A₀ → (b : ℝ)≤(N : ℝ)^A₀ →
      |(h : ℝ)|≤(N : ℝ)^A₀ →
      ((positiveSolutions a b h ⌊(N : ℝ)^A₀⌋₊).card : ℝ)≤(N : ℝ)^ε := by
  sorry

/-- The real, untruncated Griesmer sum for the actual even square-relation code. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_finite_relative_griesmer {U B t : ℕ} (hB : 1≤B) (hU : 2*B≤U)
    (ht : t≤relationRank U B) :
    (∑ i ∈ range t, (⌈(distance U B : ℝ)/(2 : ℝ)^i⌉₊ : ℝ))-(t : ℝ)≤
      (Nat.primeCounting B : ℝ)+1 := by
  sorry

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
  sorry

/-- Actual fair product law of all relative bits, and exact independence of the signs. -/
theorem _root_.PaperP1Registry.Registration.ArithmeticGeometry.local_rigidity_subcritical_relative_signs (a ε : ℝ) (ha : 0<a) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ U B : ℕ, 1≤B → a*N≤(U : ℝ) →
      (B : ℝ)≤(1-ε)*Real.log N →
      primeSignMeasure.map (relativeBits U B)=
        Measure.pi (fun _ : Fin (B-1) ↦ coordinateMeasure) ∧
      ProbabilityTheory.iIndepFun (relativeSign U B) primeSignMeasure := by
  sorry
end PaperP1Registry.RegistrationModels.ArithmeticGeometry.LocalRigidity

end ComponentLocalRigidity
