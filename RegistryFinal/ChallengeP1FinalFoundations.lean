module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring.Basic

/-! # Uniform arithmetic event structure and positive reference limits

This contained project preserves the original mathematical models and every
clause of the seven unregistered main results 2.1--2.5, 7.1 and 8.4.
Routine reference calibration is integrated into the quantitative result family.
Companion T13.1 supplies the uniform all-cardinality support count;
T15.1 and its displayed asymptotic corollary expose the fixed-moment barrier.
Model foundations retain their Paper C attribution: commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; docs/PAPER_C_REUSE.md.
All literal models precede theorem proof elaboration in both modules.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.Final.Affine

open Finset MeasureTheory

open scoped BigOperators

open scoped Classical ENNReal

open Finset MeasureTheory

open scoped Classical BigOperators

variable {ι Ω : Type*}
abbrev F₂ := ZMod 2

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance measurableF₂ : MeasurableSpace F₂ := ⊤
abbrev Sample := ℕ → F₂
def coordinateMeasure : Measure F₂ := Measure.uniformOfFinset (univ : Finset F₂)
instance coordinateProbability : IsProbabilityMeasure coordinateMeasure := by
  constructor
  rw [coordinateMeasure,Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)
def primeSignMeasure : Measure Sample := Measure.infinitePi (fun _ : ℕ ↦ coordinateMeasure)
instance primeSignProbability : IsProbabilityMeasure primeSignMeasure := by
  unfold primeSignMeasure
  infer_instance
def parity (n : ℕ) : ℕ →₀ F₂ := n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)
def valueBit (ω : Sample) (n : ℕ) : F₂ :=
  (parity n).sum fun p e ↦ ω (Nat.primeCounting' p)*e
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def startIndicator (x L : ℕ) (ω : Sample) : Bool := decide (StartEvent (valueBit ω) x L)
def runCount (N L : ℕ) (ω : Sample) : ℕ :=
  ∑ x ∈ Ico N (2*N), (startIndicator x L ω).toNat
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure
def actualMean (N L : ℕ) : ℝ := moment N L 1
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}
def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹
def indicator (x L : ℕ) (ω : Sample) : ℝ := if startIndicator x L ω then 1 else 0
def marginal (x L : ℕ) : ℝ := ∫ ω, indicator x L ω ∂primeSignMeasure
def jointMoment (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, indicator x L ω ∂primeSignMeasure
def centeredCoefficient (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicator x L ω-marginal x L) ∂primeSignMeasure
def factorialMoment (N L r : ℕ) : ℝ :=
  ∫ ω, ((runCount N L ω).descFactorial r : ℝ) ∂primeSignMeasure
def thirdCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 3-3*factorialMoment N L 2*factorialMoment N L 1+2*(factorialMoment N L 1)^3
def fourthCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 4-4*factorialMoment N L 3*factorialMoment N L 1-
    3*(factorialMoment N L 2)^2+12*factorialMoment N L 2*(factorialMoment N L 1)^2-
    6*(factorialMoment N L 1)^4
def principalSecondScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(18*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*L*(N : ℝ)^(-2/3 : ℝ)
def vertexLabel (x L : ℕ) (v : Fin (L+1)) : ℕ :=
  if v.val=0 then x-1 else x+(v.val-1)
def vertexSum (L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ v : Fin (L+1), w v
  map_add' w z := by simp only [Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c w := by
    change (∑ v : Fin (L+1), c*w v)=c*∑ v : Fin (L+1), w v
    rw [Finset.mul_sum]
def vertexParity (x L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun v ↦ parity (vertexLabel x L v))
def evenParity (x L : ℕ) : LinearMap.ker (vertexSum L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParity x L).comp (LinearMap.ker (vertexSum L)).subtype
def space (x L : ℕ) : Submodule F₂ (ℕ →₀ F₂) := LinearMap.range (evenParity x L)
def addition {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : ((i : ι) → S i) →ₗ[F₂] U where
  toFun s := ∑ i, (s i).val
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]
def RespectsRelations {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ U) (P : Finpartition (univ : Finset ι)) : Prop :=
  ∀ s : (i : ι) → S i, addition S s=0 → ∀ C ∈ P.parts, ∑ i ∈ C, (s i).val=0
def canonicalPartition {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U) : Finpartition (univ : Finset ι) :=
  ((univ : Finset (Finpartition (univ : Finset ι))).filter (RespectsRelations S)).inf id
def Connected (L : ℕ) (I : Finset ℕ) : Prop := canonicalPartition (fun i : I ↦ space i.val L)=⊤
def connectedFamilies (N L r : ℕ) : Finset (Finset ℕ) :=
  ((Ico N (2*N)).powersetCard r).filter (Connected L)
def relativeNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (addition (fun i : I ↦ space i.val L)))
def compatibleNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  I.powerset.sup fun A ↦ if 0 < jointMoment L A then relativeNullity L A else 0
def totalSpace (L : ℕ) (I : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  ⨆ i : I, space i.val L
def homogeneousMass (L : ℕ) (I : Finset ℕ) : ℝ :=
  (2 ^ Module.finrank F₂ (totalSpace L I) : ℝ)⁻¹
def rankWeight (L : ℕ) (I : Finset ℕ) : ℝ :=
  (∏ x ∈ I, marginal x L)*(2 ^ relativeNullity L I : ℝ)
def expansion_properPrefix [LinearOrder ι] (I : Finset ι) : Finset ι :=
  I.filter fun x ↦ ∃ y ∈ I, x<y
def expansion_Hereditary (D : Finset ι → Prop) : Prop :=
  ∀ ⦃I J⦄, J ⊆ I → D I → D J
def expansion_Boundary [LinearOrder ι] (D : Finset ι → Prop) (I : Finset ι) : Prop :=
  ¬ D I ∧ D (expansion_properPrefix I)
def expansion_suffix [LinearOrder ι] (G I : Finset ι) : Finset ι :=
  G.filter fun y ↦ ∀ x ∈ I, x<y
def expansion_retained (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter D
def expansion_boundary [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter (expansion_Boundary D)
abbrev expansion_SignedLaw := AddMonoidAlgebra ℝ ℕ
def expansion_scalar (r : ℝ) : expansion_SignedLaw := AddMonoidAlgebra.single 0 r
def expansion_atom (k : ℕ) : expansion_SignedLaw := AddMonoidAlgebra.single k 1
def expansion_difference : expansion_SignedLaw := expansion_atom 1-expansion_atom 0
def expansion_bernoulli (p : ℝ) : expansion_SignedLaw := expansion_atom 0+expansion_scalar p*expansion_difference
def expansion_l1Norm (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ |r|
def expansion_totalMass (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ r
def expansion_indicator (b : Bool) : ℝ := if b then 1 else 0
def expansion_count (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat
def expansion_countLaw [MeasurableSpace Ω] (G : Finset ι) (μ : Measure Ω)
    (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ k ∈ range (G.card+1), AddMonoidAlgebra.single k (μ.real {ω | expansion_count G J ω=k})
def expansion_jointMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ := ∫ ω, ∏ x ∈ I, expansion_indicator (J x ω) ∂μ
def expansion_marginal [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool) (x : ι) : ℝ :=
  ∫ ω, expansion_indicator (J x ω) ∂μ
def expansion_centeredMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ I, (expansion_indicator (J x ω)-expansion_marginal μ J x) ∂μ
def expansion_retainedReference [MeasurableSpace Ω] (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ I ∈ expansion_retained G D, expansion_scalar (expansion_jointMoment μ J I)*expansion_difference^I.card
instance finiteSpace (x L : ℕ) : Fintype (space x L) := by
  classical
  let : Fintype (LinearMap.ker (vertexSum L)) := Fintype.ofFinite _
  exact Fintype.ofSurjective (evenParity x L).rangeRestrict (by
    rintro ⟨c,⟨w,hw⟩⟩
    exact ⟨w,Subtype.ext hw⟩)
def PrimeUpTo (M : ℕ) := {p : Fin (M+1) // Nat.Prime p.val}
instance (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _
abbrev FiniteSample (M : ℕ) := PrimeUpTo M → F₂
def finiteValue (M n : ℕ) : FiniteSample M →ₗ[F₂] F₂ where
  toFun ω := ∑ p : PrimeUpTo M, ω p*parity n p.val
  map_add' := by intros; simp [add_mul,Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum,mul_assoc]
def startRow (M x L : ℕ) (i : Fin L) : FiniteSample M →ₗ[F₂] F₂ :=
  if i.val=0 then finiteValue M (x-1)+finiteValue M x
  else finiteValue M x+finiteValue M (x+i.val)
def startSystem (M x L : ℕ) : FiniteSample M →ₗ[F₂] (Fin L → F₂) := LinearMap.pi (startRow M x L)
def startRhs (L : ℕ) : Fin L → F₂ := fun i ↦ if i.val=0 then 1 else 0
def familyCentered {ι : Type*} [Fintype ι] (L : ℕ) (g : ι → ℕ) : ℝ :=
  ∫ ω, ∏ i, (indicator (g i) L ω-marginal (g i) L) ∂primeSignMeasure
def familyNullity {ι : Type*} [Fintype ι] (L : ℕ) (g : ι → ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (addition (fun i ↦ space (g i) L)))
def FullRelation {ι : Type*} [Fintype ι] (L : ℕ) (g : ι → ℕ)
    (s : (i : ι) → space (g i) L) : Prop := (∀ i, s i≠0) ∧ addition (fun i ↦ space (g i) L) s=0
def tupleSign {ι : Type*} [Fintype ι] (M L : ℕ) (g : ι → ℕ)
    (a : ι → FiniteSample M) (s : (i : ι) → space (g i) L) : ℝ :=
  ∏ i, if (∑ p : PrimeUpTo M, a i p*(s i).val p.val)=0 then 1 else -1
def partImage {I : Finset ℕ} (C : Finset I) : Finset ℕ := C.image fun i ↦ i.val

end PaperP1Registry.Final.Affine

namespace PaperP1Registry.Final.Reference

open Finset MeasureTheory

open scoped BigOperators

open scoped Classical ENNReal
abbrev F₂ := ZMod 2

local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

local instance measurableF₂ : MeasurableSpace F₂ := ⊤
abbrev Sample := ℕ → F₂
def coordinateMeasure : Measure F₂ := Measure.uniformOfFinset (univ : Finset F₂)
instance coordinateProbability : IsProbabilityMeasure coordinateMeasure := by
  constructor
  rw [coordinateMeasure,Measure.uniformOfFinset_apply]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)
def primeSignMeasure : Measure Sample := Measure.infinitePi (fun _ : ℕ ↦ coordinateMeasure)
instance primeSignProbability : IsProbabilityMeasure primeSignMeasure := by
  unfold primeSignMeasure
  infer_instance
def parity (n : ℕ) : ℕ →₀ F₂ := n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)
def valueBit (ω : Sample) (n : ℕ) : F₂ :=
  (parity n).sum fun p e ↦ ω (Nat.primeCounting' p)*e
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x
def startIndicator (x L : ℕ) (ω : Sample) : Bool := decide (StartEvent (valueBit ω) x L)
def runCount (N L : ℕ) (ω : Sample) : ℕ :=
  ∑ x ∈ Ico N (2*N), (startIndicator x L ω).toNat
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure
def actualMean (N L : ℕ) : ℝ := moment N L 1
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}
def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹
def indicator (x L : ℕ) (ω : Sample) : ℝ := if startIndicator x L ω then 1 else 0
def marginal (x L : ℕ) : ℝ := ∫ ω, indicator x L ω ∂primeSignMeasure
def jointMoment (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, indicator x L ω ∂primeSignMeasure
def centeredCoefficient (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicator x L ω-marginal x L) ∂primeSignMeasure
def factorialMoment (N L r : ℕ) : ℝ :=
  ∫ ω, ((runCount N L ω).descFactorial r : ℝ) ∂primeSignMeasure
def thirdCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 3-3*factorialMoment N L 2*factorialMoment N L 1+2*(factorialMoment N L 1)^3
def fourthCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 4-4*factorialMoment N L 3*factorialMoment N L 1-
    3*(factorialMoment N L 2)^2+12*factorialMoment N L 2*(factorialMoment N L 1)^2-
    6*(factorialMoment N L 1)^4
def principalSecondScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(18*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*L*(N : ℝ)^(-2/3 : ℝ)
def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)
def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k
def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)
def quadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|
def channelWeight (d : ℕ) : ℤ := if d=1 then 1 else (2 : ℤ)^(d-2)
def channelSum (L a b s : ℤ) (m : ℕ) : ℤ :=
  ∑ d ∈ range m, channelWeight (d+1)*(L+s-a*((d+1 : ℕ) : ℤ))*(L+s-b*((d+1 : ℕ) : ℤ))
def unsignedChannel (L a b : ℕ) : ℤ := channelSum L a b 1 (L/b)
def signedChannel (L a b : ℕ) : ℤ := channelSum L a b (-1) (L/b)
def numerators (b : ℕ) : Finset ℕ := (Icc 1 (b-1)).filter fun a ↦ b<2*a ∧ a.Coprime b
def orientationWeight (a b : ℕ) : ℝ := 2*(2*(a : ℝ)-b)/((a : ℝ)*b)
def heightSum (b L : ℕ) : ℝ := ∑ a ∈ numerators b, orientationWeight a b*(signedChannel L a b : ℝ)
def coefficient (N L h : ℕ) : ℝ := (nominalMean N L)^2/N*∑ b ∈ Icc 3 h, heightSum b L
def twoChannelCoefficient (N L : ℕ) : ℝ := (nominalMean N L)^2/(3*N)*
  ((signedChannel L 2 3 : ℝ)+(signedChannel L 3 4 : ℝ))
def correction (N L : ℕ) : ℝ := (nominalMean N L)^2/N*heightSum 5 L
def heightMass (N L b : ℕ) : ℝ := (nominalMean N L)^2/N*heightSum b L
def phaseSum (b : ℕ) : ℝ := ∑ a ∈ numerators b, (2*(a : ℝ)-b)*((b : ℝ)-a)/a
def phaseConstant (b r : ℕ) : ℝ := ((b : ℝ)+r-1)/((b : ℝ)^2*(2 : ℝ)^((r : ℝ)/b))*phaseSum b
def phaseMass (N L b : ℕ) : ℝ := phaseConstant b (L%b)*
  (nominalMean N L)^(2-1/(b : ℝ))*L*(N : ℝ)^(-1+1/(b : ℝ))
def sourceMeasure (N L : ℕ) : Measure ℕ := primeSignMeasure.map (runCount N L)
instance sourceFinite (N L : ℕ) : IsFiniteMeasure (sourceMeasure N L) := by
  unfold sourceMeasure;infer_instance
def sourceSigned (N L : ℕ) : SignedMeasure ℕ := (sourceMeasure N L).toSignedMeasure
def signedReference (μ α : ℝ) : SignedMeasure ℕ := Measure.count.withDensityᵥ (quadraticMass μ α)
def differenceMap : SignedMeasure ℕ →ₗ[ℝ] SignedMeasure ℕ := VectorMeasure.mapₗ Nat.succ-LinearMap.id
def secondDifference (μ : ℝ) : SignedMeasure ℕ :=
  differenceMap (differenceMap (Measure.count.withDensityᵥ (poissonMass μ)))
def distance (ν κ : SignedMeasure ℕ) : ℝ := ∑' k : ℕ, |ν {k}-κ {k}|
def secondNorm (μ : ℝ) : ℝ := ∑' k : ℕ, |secondDifference μ {k}|
def totalVariation (N L : ℕ) (Q : ProbabilityMeasure ℕ) : ℝ :=
  (∑' k : ℕ, |(sourceMeasure N L).real {k}-(Q : Measure ℕ).real {k}|)/2
def leadingGap (N L h : ℕ) : ℝ := phaseMass N L (h+1)/2*secondNorm (nominalMean N L)
def hermiteLaw (μ α : ℝ) (hα : 0≤α) (hαμ : α≤μ) : ProbabilityMeasure ℕ :=
  let A : ProbabilityMeasure ℕ := ⟨ProbabilityTheory.poissonMeasure ⟨μ-α,sub_nonneg.mpr hαμ⟩,
    ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure _⟩
  let B : ProbabilityMeasure ℕ := ⟨ProbabilityTheory.poissonMeasure ⟨α/2,div_nonneg hα (by norm_num)⟩,
    ProbabilityTheory.instIsProbabilityMeasureNatPoissonMeasure _⟩
  let P : ProbabilityMeasure (ℕ×ℕ) := ⟨(A : Measure ℕ).prod (B : Measure ℕ),inferInstance⟩
  P.map (fun z : ℕ×ℕ ↦ z.1+2*z.2)
def fractionalPart (μ : ℝ) : ℝ := μ-⌊μ⌋₊

end PaperP1Registry.Final.Reference

namespace PaperP1Registry.Final.Affine

open Finset
open scoped BigOperators Classical

/-- Every effective projection is nonzero; no affine compatibility is required. -/
def supportFullRelation (L : ℕ) (I : Finset ℕ) : Prop :=
  ∃ u : (i : I) → space i.val L, (∀ i, u i ≠ 0) ∧ (∑ i : I, (u i).val)=0
def supportTupleSet {r : ℕ} (n : Fin r → ℕ) : Finset ℕ := univ.image n
def supportLists (G : Finset ℕ) (L r : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ : Fin r ↦ G).filter fun n ↦
    Function.Injective n ∧ supportFullRelation L (supportTupleSet n)
/-- Ordered distinct regular starts, strict separation >L and full effective support. -/
def fullSupportLists (G : Finset ℕ) (L r : ℕ) : Finset (Fin r → ℕ) :=
  (supportLists G L r).filter fun n ↦
    (∀ i, Module.finrank F₂ (space (n i) L)=L) ∧
      ∀ i j, i≠j → L<Nat.dist (n i) (n j)

end PaperP1Registry.Final.Affine

namespace PaperP1Registry.Final.Obstruction

open MeasureTheory Filter Asymptotics
open scoped BigOperators Classical Topology

/-- Quadratic Poisson reference at mean one; this is not the arithmetic run law. -/
def baseMass (a : ℝ) : ℕ → ℝ := PaperP1Registry.Final.Reference.quadraticMass 1 a
def differenceCoefficient (m k : ℕ) : ℝ := (-1 : ℝ)^(m-k)*(m.choose k : ℝ)
def epsilon (m : ℕ) (a : ℝ) : ℝ := (1-a/2)*Real.exp (-1)/(2*(m.factorial : ℝ))
def perturbedMass (m : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  baseMass a k+epsilon m a*differenceCoefficient m k
def IsProbabilityMass (p : ℕ → ℝ) : Prop := (∀ k,0≤p k) ∧ HasSum p 1
def factorialMoment (p : ℕ → ℝ) (j : ℕ) : ℝ := ∑' k, p k*(k.descFactorial j : ℝ)
def exponentialMoment (p : ℕ → ℝ) (t : ℝ) : ℝ := ∑' k, p k*Real.exp (t*k)
def variation (p q : ℕ → ℝ) : ℝ := (∑' k,|p k-q k|)/2
def exponentialBound (t : ℝ) : ℝ :=
  3/2*Real.exp (Real.exp t-1)*(1+(1/2)*(Real.exp t-1)^2)
def order (N : ℕ) : ℕ := ⌊Real.sqrt (Real.log N)⌋₊
def parameter (N : ℕ) : ℝ := Real.log N*(N : ℝ)^(-(2/3 : ℝ))
def Valid (N : ℕ) : Prop := 3≤order N ∧ 0≤parameter N ∧ parameter N≤1
/-- Poisson(1) at the finitely many invalid initial indices. -/
def familyMass (N k : ℕ) : ℝ := if Valid N then perturbedMass (order N) (parameter N) k
  else PaperP1Registry.Final.Reference.poissonMass 1 k
def referenceMass (N k : ℕ) : ℝ := if Valid N then baseMass (parameter N) k
  else PaperP1Registry.Final.Reference.poissonMass 1 k
def familyDistance (N : ℕ) : ℝ := variation (familyMass N) (referenceMass N)

end PaperP1Registry.Final.Obstruction

namespace PaperP1Registry.Final.Affine

open Finset MeasureTheory
open scoped BigOperators Classical ENNReal
variable {ι Ω : Type*}

/-- Complete affine event calculus, including the all-subfamilies arithmetic envelope.
Centered expansions and factorization are auxiliary clauses of this structure. -/
theorem uniform_event_calculus :
  (∀ [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (_hJ : ∀ x, Measurable (J x)),
    (∀ k, (expansion_countLaw G μ J).coeff k=μ.real {ω | expansion_count G J ω=k}) ∧
    (∀ k, 0 ≤ (expansion_countLaw G μ J).coeff k) ∧ expansion_totalMass (expansion_countLaw G μ J)=1 ∧
    expansion_countLaw G μ J=∑ I ∈ G.powerset, expansion_scalar (expansion_centeredMoment μ J I)*
      expansion_difference^I.card*∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x))
  ∧ (∀ {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace Ω] (G : Finset κ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : κ → Ω → Bool) (_hJ : ∀ x, Measurable (J x)),
    expansion_centeredMoment μ J ∅=1 ∧
    (∀ x, expansion_centeredMoment μ J {x}=0) ∧
    ∀ I : Finset κ,
      (∀ k, 0≤(∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x)).coeff k) ∧
      expansion_totalMass (∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x))=1)
  ∧ (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (_hL : 0 < L) (_hcut : ∀ i, g i+L ≤ M)
    (_hp : ∀ i, 0 < marginal (g i) L),
    ∃ a : ι → FiniteSample M, (∀ i, startSystem M (g i) L (a i)=startRhs L) ∧
      familyCentered L g=(∏ i, marginal (g i) L)*
        (∑ s : (i : ι) → space (g i) L, if FullRelation L g s then tupleSign M L g a s else 0) ∧
      |familyCentered L g| ≤ (∏ i, marginal (g i) L)*((2 ^ familyNullity L g : ℝ)-1) ∧
      |familyCentered L g| ≤ (∏ i, marginal (g i) L)*(2 ^ familyNullity L g : ℝ) ∧
      (familyCentered L g≠0 → ∃ s : (i : ι) → space (g i) L, FullRelation L g s))
  ∧ (∀ (L : ℕ) (_hL : 0 < L) (I : Finset ℕ) (_hne : I.Nonempty),
    homogeneousMass L I=(∏ x ∈ I, (2 ^ Module.finrank F₂ (space x L) : ℝ)⁻¹)*
      (2 ^ relativeNullity L I : ℝ) ∧
    rankWeight L I ≤ homogeneousMass L I ∧ jointMoment L I ≤ homogeneousMass L I ∧
      |centeredCoefficient L I| ≤ homogeneousMass L I)
  ∧ (∀ (C : ℝ),
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ Ico N (2*N) →
        homogeneousMass L I ≤ (2 : ℝ)^I.card*((2 ^ L : ℝ)⁻¹)^I.card*
          (2 ^ relativeNullity L I : ℝ))
  ∧ (∀ (L : ℕ) (_hL : 0 < L) (I : Finset ℕ)
    (_hp : ∀ x ∈ I, 0 < marginal x L),
    |centeredCoefficient L I| ≤ (2 : ℝ)^I.card*(∏ x ∈ I, marginal x L)*
      (2 ^ compatibleNullity L I : ℝ) ∧
    compatibleNullity L I ≤ relativeNullity L I ∧
    (0 < jointMoment L I → compatibleNullity L I=relativeNullity L I))
  ∧ (∀ {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U),
    ∃! P : Finpartition (univ : Finset ι), RespectsRelations S P ∧
      ∀ Q : Finpartition (univ : Finset ι), RespectsRelations S Q → P ≤ Q)
  ∧ (∀ (L : ℕ) (_hL : 0 < L) (I : Finset ℕ),
    let P := canonicalPartition (fun i : I ↦ space i.val L)
    RespectsRelations (fun i : I ↦ space i.val L) P ∧
    (∀ Q : Finpartition (univ : Finset I), RespectsRelations (fun i : I ↦ space i.val L) Q → P ≤ Q) ∧
    jointMoment L I=∏ C ∈ P.parts, jointMoment L (partImage C) ∧
    centeredCoefficient L I=∏ C ∈ P.parts, centeredCoefficient L (partImage C) ∧
    relativeNullity L I=∑ C ∈ P.parts, relativeNullity L (partImage C))
  ∧ (∀ (C u ε : ℝ) (_hu : 0<u) (_hε : 0<ε),
    ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C → ∀ G : Finset ℕ, G⊆Ico N (2*N) →
      ∀ s : ℕ, 2≤s →
      (∑ r ∈ Icc s G.card, (u^r/(r.factorial : ℝ))*
        ((fullSupportLists G L r).card*((2^L : ℝ)⁻¹)^r)) ≤
          (N : ℝ)^(-min ((s : ℝ)/2) 2+ε)) :=
by sorry

end PaperP1Registry.Final.Affine

namespace PaperP1Registry.Final.Reference

open Finset MeasureTheory
open scoped BigOperators Classical ENNReal

/-- Positive reference calibration and the quantitative Hermite approximation family.
The exact positivity interval is an auxiliary calibration clause; the arithmetic
approximation bounds and moving-phase equivalents are the principal conclusions. -/
theorem positive_hermite_approximation :
  (∀ (μ α : ℝ) (_hμ : 0<μ),
    ((∀ k : ℕ, 0≤quadraticMass μ α k) ∧ HasSum (quadraticMass μ α) 1) ↔
      0≤α ∧ α≤2*μ^2/(μ+fractionalPart μ*(1-fractionalPart μ)))
  ∧ (∀ (μ α : ℝ) (_hμ : 0<μ) (k : ℕ),
    signedReference μ α {k}=Real.exp (-μ)*μ^k/(k.factorial : ℝ)*
      (1+α/(2*μ^2)*(((k : ℝ)-μ)^2-k)))
  ∧ (∀ (C ε : ℝ) (_hε : 0<ε),
    ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤secondCumulant N L, ∃ hαμ : secondCumulant N L≤actualMean N L,
      distance (sourceSigned N L)
        (hermiteLaw (actualMean N L) (secondCumulant N L) hα hαμ : Measure ℕ).toSignedMeasure ≤
          (N : ℝ)^(-4/3+ε) ∧
      totalVariation N L (hermiteLaw (actualMean N L) (secondCumulant N L) hα hαμ) ≤
        (N : ℝ)^(-4/3+ε))
  ∧ (∀ (h : ℕ) (_hh : 3≤h) (C ε : ℝ) (_hε : 0<ε),
    ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤coefficient N L h, ∃ hαμ : coefficient N L h≤nominalMean N L,
      distance (sourceSigned N L)
        (hermiteLaw (nominalMean N L) (coefficient N L h) hα hαμ : Measure ℕ).toSignedMeasure ≤
          (N : ℝ)^(-1+1/((h+1 : ℕ) : ℝ)+ε))
  ∧ (∀ (h : ℕ) (_hh : 3≤h) (C : ℝ),
    ∀ τ : ℝ, 0<τ → ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤coefficient N L h, ∃ hαμ : coefficient N L h≤nominalMean N L,
      0<leadingGap N L h ∧
      |totalVariation N L (hermiteLaw (nominalMean N L) (coefficient N L h) hα hαμ)/
        (phaseMass N L (h+1)*secondNorm (nominalMean N L)/4)-1| ≤ τ) :=
by sorry

end PaperP1Registry.Final.Reference

namespace PaperP1Registry.Final.Obstruction

open MeasureTheory Filter Asymptotics
open scoped BigOperators Classical Topology

/-- Companion T15.1 and its displayed growing-order corollary. Every probability
and summability assertion is included. Fixed orders precede their thresholds;
this family is not claimed to have a multiplicative realization. -/
theorem fixed_moment_barrier :
    (∀ m : ℕ, 3≤m → ∀ a : ℝ, 0≤a → a≤1 →
      IsProbabilityMass (baseMass a) ∧ IsProbabilityMass (perturbedMass m a) ∧
      (∀ k : ℕ, baseMass a k/2≤perturbedMass m a k ∧
        perturbedMass m a k≤3/2*baseMass a k) ∧
      (∀ j : ℕ, Summable (fun k ↦ perturbedMass m a k*(k.descFactorial j : ℝ)) ∧
        Summable (fun k ↦ baseMass a k*(k.descFactorial j : ℝ)) ∧
        ((factorialMoment (perturbedMass m a) j=factorialMoment (baseMass a) j) ↔ j≠m)) ∧
      variation (perturbedMass m a) (baseMass a)=
        (1-a/2)*(2 : ℝ)^(m-2)/(Real.exp 1*(m.factorial : ℝ)) ∧
      (∀ t : ℝ, 0≤t → Summable (fun k ↦ perturbedMass m a k*Real.exp (t*k)) ∧
        exponentialMoment (perturbedMass m a) t≤exponentialBound t)) ∧
    (∀ N : ℕ, IsProbabilityMass (familyMass N) ∧ IsProbabilityMass (referenceMass N)) ∧
    (∀ r : ℕ, ∀ᶠ N : ℕ in atTop,
      Summable (fun k ↦ familyMass N k*(k.descFactorial r : ℝ)) ∧
      factorialMoment (familyMass N) r=1+(r.choose 2 : ℝ)*parameter N) ∧
    (∀ t : ℝ, 0≤t → ∀ᶠ N : ℕ in atTop,
      Summable (fun k ↦ familyMass N k*Real.exp (t*k)) ∧
      exponentialMoment (familyMass N) t≤exponentialBound t) ∧
    ((fun N : ℕ ↦ Real.log (familyDistance N)+(1/2)*Real.sqrt (Real.log N)*Real.log (Real.log N))
      =O[atTop] (fun N : ℕ ↦ Real.sqrt (Real.log N))) ∧
    (∀ γ : ℝ, 0<γ → ∃ N₀ : ℕ, ∀ N≥N₀, (N : ℝ)^(-γ)<familyDistance N) :=
by sorry

end PaperP1Registry.Final.Obstruction
