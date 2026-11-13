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
public import PaperP1.Algebra.StoppedExpansion
public import PaperP1.Asymptotics.ActualPairPhase
public import PaperP1.Asymptotics.FixedHeightHierarchy
public import PaperP1.Asymptotics.MomentObstructionSequence
public import PaperP1.Asymptotics.OptimalHermite
public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Asymptotics.OptimalThirdCumulant
public import PaperP1.Asymptotics.TwoChannelReference
public import PaperP1.Asymptotics.UniformFullSupportCount
public import PaperP1.Asymptotics.V2HomogeneousEnvelope
public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Model.RetainedMomentTransfer
public import PaperP1.Model.SquareClassFourier
public import PaperP1.Model.UnrestrictedRunComponents
public import PaperP1.Probability.CenteredMeasureExpansion
public import PaperP1.Probability.StoppedMeasureLaw

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

theorem runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω=PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem factorialMoment_eq (N L r : ℕ) :
    factorialMoment N L r=PaperP1.FactorialCountMoments.factorialCountMoment (PaperP1.Model.dyadicBlock N) L r := by rfl

theorem marginal_eq (x L : ℕ) : marginal x L=PaperP1.Model.InfiniteStarts.infiniteMarginal x L := by rfl

theorem jointMoment_eq (L : ℕ) (A : Finset ℕ) :
    jointMoment L A=PaperP1.Model.InfiniteStarts.infiniteJointMoment L A := by rfl

theorem centeredCoefficient_eq (L : ℕ) (A : Finset ℕ) :
    centeredCoefficient L A=PaperP1.Model.InfiniteStarts.infiniteCenteredCoefficient L A := by rfl

theorem third_eq (N L : ℕ) : thirdCumulant N L=
    PaperP1.ThirdRunFactorialCumulant.thirdFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem fourth_eq (N L : ℕ) : fourthCumulant N L=
    PaperP1.FourthRunFactorialCumulant.fourthFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem second_eq (N L : ℕ) : secondCumulant N L=
    PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem principalScale_eq (N L : ℕ) : principalSecondScale N L=
    PaperP1.ChannelMassPhaseEquivalent.phaseMass N L 3 := by
  exact (PaperP1.PrincipalPairPhaseComparison.phase_three N L).symm

theorem factorial_source (N L r : ℕ) :
    Integrable (fun ω ↦ ((runCount N L ω).descFactorial r : ℝ)) primeSignMeasure ∧
    factorialMoment N L r=(r.factorial : ℝ)*
      ∑ A ∈ (Ico N (2*N)).powersetCard r, jointMoment L A :=
by
  constructor
  · exact PaperP1.RetainedMomentTransfer.original_observable_integrable
      (PaperP1.Model.dyadicBlock N) L (fun n : ℕ ↦ (n.descFactorial r : ℝ))
  · simpa only [factorialMoment_eq,jointMoment_eq,PaperP1.Model.dyadicBlock] using
      (PaperP1.FactorialCountMoments.factorialCountMoment_eq_subset
        (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl r)

theorem third_exact_identity (N L : ℕ) :
    thirdCumulant N L=
      6*(∑ A ∈ (Ico N (2*N)).powersetCard 3, centeredCoefficient L A)-
      6*(∑ e ∈ (Ico N (2*N)).powersetCard 2,
        (∑ x ∈ e, marginal x L)*centeredCoefficient L e)+
      2*∑ x ∈ Ico N (2*N), (marginal x L)^3 :=
by
  simpa only [third_eq,centeredCoefficient_eq,marginal_eq,PaperP1.Model.dyadicBlock] using
    (PaperP1.ThirdRunFactorialCumulant.exact_formula
      (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl)

theorem fourth_exact_identity (N L : ℕ) :
    fourthCumulant N L=
      24*(∑ A ∈ (Ico N (2*N)).powersetCard 4, centeredCoefficient L A)-
      12*(∑ e ∈ (Ico N (2*N)).powersetCard 2, centeredCoefficient L e)^2-
      24*(∑ A ∈ (Ico N (2*N)).powersetCard 3,
        centeredCoefficient L A*∑ x ∈ A, marginal x L)+
      24*(∑ e ∈ (Ico N (2*N)).powersetCard 2,
        ((∑ x ∈ e, (marginal x L)^2)+∏ x ∈ e, marginal x L)*centeredCoefficient L e)-
      6*∑ x ∈ Ico N (2*N), (marginal x L)^4 :=
by
  simpa only [fourth_eq,centeredCoefficient_eq,marginal_eq,PaperP1.Model.dyadicBlock] using
    (PaperP1.FourthRunFactorialCumulant.exact_formula
      (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl)

theorem principal_second_equivalent (C τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      0 < principalSecondScale N L ∧ |secondCumulant N L/principalSecondScale N L-1| ≤ τ :=
by
  obtain ⟨N₀,h₀,h⟩ := PaperP1.ActualPairPhase.uniform_phases C τ hτ
  refine ⟨N₀,h₀,?_⟩
  intro N hN L hBand
  obtain ⟨hpos,_hpos4,hrel,_hrel4⟩ := h N hN L hBand
  simpa only [principalScale_eq,second_eq,PaperP1.ActualPairPhase.alpha_eq_cumulant] using
    And.intro hpos hrel

theorem optimal_third_cumulant (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      c*(N : ℝ)^(-41/30 : ℝ) ≤ thirdCumulant N L ∧
        thirdCumulant N L ≤ (N : ℝ)^(-41/30+ε) :=
by
  refine ⟨PaperP1.OptimalThirdCumulant.lowerConstant C,
    PaperP1.OptimalThirdCumulant.lowerConstant_pos C,?_⟩
  intro ε hε
  obtain ⟨N₀,h₀,h⟩ := PaperP1.OptimalThirdCumulant.article_14_1 C ε hε
  refine ⟨N₀,h₀,?_⟩
  intro N hN L hBand
  simpa only [third_eq] using h N hN L hBand

theorem space_eq (x L : ℕ) : space x L=PaperP1.Arithmetic.squareClassSpace x L := by rfl

theorem addition_eq {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : addition S=PaperP1.Affine.relationAddition S := by rfl

theorem canonicalPartition_eq {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U) :
    canonicalPartition S=PaperP1.Affine.canonicalRelationPartition S := by rfl

theorem connected_eq (L : ℕ) (I : Finset ℕ) :
    Connected L I=PaperP1.ConnectedWindowFamilies.Connected L I := by rfl

theorem connectedFamilies_eq (N L r : ℕ) : connectedFamilies N L r=
    PaperP1.ConnectedWindowFamilies.connectedFamilies (PaperP1.Model.dyadicBlock N) L r := by rfl

theorem relativeNullity_eq (L : ℕ) (I : Finset ℕ) :
    relativeNullity L I=PaperP1.Model.InfiniteStarts.runRelativeNullity L I := by rfl

theorem compatibleNullity_eq (L : ℕ) (I : Finset ℕ) :
    compatibleNullity L I=PaperP1.Model.InfiniteStarts.runCompatibleNullity L I := by rfl

theorem homogeneousMass_eq (L : ℕ) (I : Finset ℕ) :
    homogeneousMass L I=PaperP1.HomogeneousRunMass.probability L I := by
  rw [PaperP1.HomogeneousRunMass.probability_rank]
  rfl

theorem rankWeight_eq (L : ℕ) (I : Finset ℕ) :
    rankWeight L I=PaperP1.PrimitiveWindowMass.weight L I := by rfl

theorem expansion_reconstruct (ν : expansion_SignedLaw) (n : ℕ)
    (hν : ∀ k, n<k → ν.coeff k=0) :
    ν=∑ k ∈ range (n+1), AddMonoidAlgebra.single k (ν.coeff k) := by
  classical
  have hs : ν.coeff.support ⊆ range (n+1) := by
    intro k hk
    apply mem_range.mpr
    by_contra h
    have hz := hν k (by omega)
    exact (Finsupp.mem_support_iff.mp hk) hz
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single ν]
  exact Finsupp.sum_of_support_subset _ hs _ (fun _ _ ↦ by simp)

theorem expansion_countLaw_eq_source [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    expansion_countLaw G μ J=PaperP1.Probability.observedCountLaw G μ J hJ := by
  have h := expansion_reconstruct (PaperP1.Probability.observedCountLaw G μ J hJ) G.card
    (fun k hk ↦ PaperP1.Probability.countLaw_coeff_eq_zero_of_card_lt G
      (PaperP1.Probability.indicatorObservationProbability μ J hJ).weight
      (fun x σ ↦ σ x) hk)
  rw [h]
  unfold expansion_countLaw
  apply Finset.sum_congr rfl
  intro k _
  rw [PaperP1.Probability.observedCountLaw_coeff]
  rfl

theorem expansion_totalMass_eq_source (ν : expansion_SignedLaw) :
    expansion_totalMass ν=PaperP1.Probability.totalMass ν :=
  (PaperP1.Probability.totalMass_eq_sum_coeff ν).symm

theorem expansion_l1Norm_eq_source (ν : expansion_SignedLaw) :
    expansion_l1Norm ν=PaperP1.Probability.l1Norm ν := rfl

theorem expansion_retainedReference_eq_source [MeasurableSpace Ω]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω)
    (J : ι → Ω → Bool) :
    expansion_retainedReference G D μ J=PaperP1.Probability.measureRetainedReference G D μ J := rfl

theorem expansion_jointMoment_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    expansion_jointMoment μ J I=PaperP1.Probability.measureJointMoment μ J I := rfl

theorem expansion_marginal_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (x : ι) :
    expansion_marginal μ J x=PaperP1.Probability.measureMarginal μ J x := rfl

theorem expansion_centeredMoment_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    expansion_centeredMoment μ J I=PaperP1.Probability.measureCenteredMoment μ J
      (PaperP1.Probability.measureMarginal μ J) I := rfl

theorem expansion_boundary_eq_source [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) :
    expansion_boundary G D=PaperP1.Algebra.boundarySets G D := rfl

theorem expansion_polynomial_expansion {R : Type*} [LinearOrder ι] [CommSemiring R]
    (G : Finset ι) (D : Finset ι → Prop) (u : ι → R) (t : R)
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    (∏ x ∈ G, (1+t*u x))=
      (∑ I ∈ expansion_retained G D, t^I.card*∏ x ∈ I, u x)+
      ∑ I ∈ expansion_boundary G D, (t^I.card*∏ x ∈ I, u x)*
        ∏ y ∈ expansion_suffix G I, (1+t*u y) :=
by
  exact PaperP1.Algebra.stopped_expansion G D u t hD h0

theorem expansion_centered_identity [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    (∀ k, (expansion_countLaw G μ J).coeff k=μ.real {ω | expansion_count G J ω=k}) ∧
    (∀ k, 0 ≤ (expansion_countLaw G μ J).coeff k) ∧ expansion_totalMass (expansion_countLaw G μ J)=1 ∧
    expansion_countLaw G μ J=∑ I ∈ G.powerset, expansion_scalar (expansion_centeredMoment μ J I)*
      expansion_difference^I.card*∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x) :=
by
  rw [expansion_countLaw_eq_source G μ J hJ]
  have hp := PaperP1.Probability.observedCountLaw_isProbability G μ J hJ
  refine ⟨?_,hp.1,?_,?_⟩
  · intro k
    exact PaperP1.Probability.observedCountLaw_coeff G μ J hJ k
  · rw [expansion_totalMass_eq_source]
    exact hp.2
  · exact PaperP1.Probability.centered_measure_expansion G μ J hJ

theorem expansion_positive_stopped_kernel [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    expansion_totalMass (expansion_retainedReference G D μ J)=1 ∧
    ∃ K : Finset ι → expansion_SignedLaw,
      expansion_countLaw G μ J-expansion_retainedReference G D μ J=
        ∑ I ∈ expansion_boundary G D, expansion_difference^I.card*K I ∧
      (∀ I k, (K I).coeff k=∫ ω, (∏ x ∈ I, expansion_indicator (J x ω))*
        (if expansion_count (expansion_suffix G I) J ω=k then 1 else 0) ∂μ) ∧
      ∀ I, (∀ k, 0 ≤ (K I).coeff k) ∧
        expansion_totalMass (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} ∧
        expansion_l1Norm (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by
  constructor
  · rw [expansion_totalMass_eq_source,expansion_retainedReference_eq_source]
    exact PaperP1.Probability.measureRetainedReference_mass G D μ J hJ h0
  · refine ⟨PaperP1.Probability.measureBoundaryKernel G μ J hJ,?_,?_,?_⟩
    · rw [expansion_countLaw_eq_source G μ J hJ,expansion_retainedReference_eq_source]
      exact PaperP1.Probability.stopped_measure_count_difference G D μ J hJ hD h0
    · intro I k
      exact PaperP1.Probability.measureBoundaryKernel_coeff G μ J hJ I k
    · intro I
      refine ⟨PaperP1.Probability.measureBoundaryKernel_nonneg G μ J hJ I,?_,?_⟩
      · rw [expansion_totalMass_eq_source,PaperP1.Probability.measureBoundaryKernel_mass,
          PaperP1.Probability.measureJointMoment_eq_probability μ J hJ]
      · rw [expansion_l1Norm_eq_source,PaperP1.Probability.measureBoundaryKernel_l1Norm,
          PaperP1.Probability.measureJointMoment_eq_probability μ J hJ]

theorem expansion_stopped_l1_bound [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    expansion_l1Norm (expansion_countLaw G μ J-expansion_retainedReference G D μ J) ≤
      ∑ I ∈ expansion_boundary G D, (2 : ℝ)^I.card*μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by
  rw [expansion_l1Norm_eq_source,expansion_countLaw_eq_source G μ J hJ,expansion_retainedReference_eq_source,expansion_boundary_eq_source]
  simpa only [PaperP1.Probability.measureJointMoment_eq_probability μ J hJ] using
    PaperP1.Probability.stopped_measure_count_l1_bound G D μ J hJ hD h0

theorem tupleSign_eq {ι : Type*} [Fintype ι] (M L : ℕ) (g : ι → ℕ)
    (a : ι → FiniteSample M) (s : (i : ι) → space (g i) L) :
    tupleSign M L g a s=PaperP1.Model.InfiniteStarts.squareClassTupleSign M L g a s := by
  unfold tupleSign PaperP1.Model.InfiniteStarts.squareClassTupleSign
  apply Finset.prod_congr rfl
  intro i _
  have hpair : ((PaperP1.Model.parityPairing M) (s i).val) (a i)=
      ∑ p : PrimeUpTo M, a i p*(s i).val p.val := by rfl
  simp only [PaperP1.Affine.realCharacter,PaperP1.Affine.binarySign,Int.cast_ite,
    Int.cast_one,Int.cast_neg]
  rw [hpair]

theorem original_fourier {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (hcut : ∀ i, g i+L ≤ M)
    (hp : ∀ i, 0 < marginal (g i) L) :
    ∃ a : ι → FiniteSample M, (∀ i, startSystem M (g i) L (a i)=startRhs L) ∧
      familyCentered L g=(∏ i, marginal (g i) L)*
        (∑ s : (i : ι) → space (g i) L, if FullRelation L g s then tupleSign M L g a s else 0) ∧
      |familyCentered L g| ≤ (∏ i, marginal (g i) L)*((2 ^ familyNullity L g : ℝ)-1) ∧
      |familyCentered L g| ≤ (∏ i, marginal (g i) L)*(2 ^ familyNullity L g : ℝ) ∧
      (familyCentered L g≠0 → ∃ s : (i : ι) → space (g i) L, FullRelation L g s) := by
  obtain ⟨a,ha,hformula,hminus,hcoarse,hrel⟩ :=
    PaperP1.Model.InfiniteStarts.full_support_squareClass_fourier M L g hL hcut hp
  refine ⟨a,ha,?_,hminus,hcoarse,hrel⟩
  calc
    familyCentered L g=(∏ i, marginal (g i) L)*
      (∑ s : (i : ι) → space (g i) L, if FullRelation L g s then
        PaperP1.Model.InfiniteStarts.squareClassTupleSign M L g a s else 0) := hformula
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      split_ifs
      · exact (tupleSign_eq M L g a s).symm
      · rfl

theorem finite_envelope (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hne : I.Nonempty) :
    homogeneousMass L I=(∏ x ∈ I, (2 ^ Module.finrank F₂ (space x L) : ℝ)⁻¹)*
      (2 ^ relativeNullity L I : ℝ) ∧
    rankWeight L I ≤ homogeneousMass L I ∧ jointMoment L I ≤ homogeneousMass L I ∧
      |centeredCoefficient L I| ≤ homogeneousMass L I := by
  have h := PaperP1.V2HomogeneousEnvelope.finite_domination L hL I hne
  refine ⟨?_,?_,?_,?_⟩
  · have hd (x : ℕ) : Module.finrank F₂ (space x L)=
        Module.finrank F₂ (PaperP1.Arithmetic.squareClassSpace x L) := by rw [space_eq]
    simpa only [homogeneousMass_eq,hd,relativeNullity_eq,
      PaperP1.Model.InfiniteStarts.runRelativeNullity] using h.1
  · simpa only [rankWeight_eq,homogeneousMass_eq] using h.2.1
  · simpa only [jointMoment_eq,homogeneousMass_eq] using h.2.2.1
  · simpa only [centeredCoefficient_eq,homogeneousMass_eq] using h.2.2.2

theorem nominal_envelope (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ Ico N (2*N) →
        homogeneousMass L I ≤ (2 : ℝ)^I.card*((2 ^ L : ℝ)⁻¹)^I.card*
          (2 ^ relativeNullity L I : ℝ) := by
  simpa only [homogeneousMass_eq,relativeNullity_eq,PaperP1.PrimitiveNominalMass.weight,
    PaperP1.Model.InfiniteStarts.runRelativeNullity,PaperP1.Model.dyadicBlock,mul_assoc] using
    PaperP1.V2HomogeneousEnvelope.uniform_nominal_comparison C

theorem compatible_nullity (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < marginal x L) :
    |centeredCoefficient L I| ≤ (2 : ℝ)^I.card*(∏ x ∈ I, marginal x L)*
      (2 ^ compatibleNullity L I : ℝ) ∧
    compatibleNullity L I ≤ relativeNullity L I ∧
    (0 < jointMoment L I → compatibleNullity L I=relativeNullity L I) := by
  exact ⟨PaperP1.Model.InfiniteStarts.infinite_centered_compatible_nullity_bound L I hL hp,
    PaperP1.Model.InfiniteStarts.runCompatibleNullity_le_relative L I,
    PaperP1.Model.InfiniteStarts.runCompatibleNullity_eq_of_positive_joint L I⟩

theorem unique_direct_partition {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U) :
    ∃! P : Finpartition (univ : Finset ι), RespectsRelations S P ∧
      ∀ Q : Finpartition (univ : Finset ι), RespectsRelations S Q → P ≤ Q := by
  exact PaperP1.Affine.existsUnique_finest_relationPartition S

theorem canonical_factorization (L : ℕ) (hL : 0 < L) (I : Finset ℕ) :
    let P := canonicalPartition (fun i : I ↦ space i.val L)
    RespectsRelations (fun i : I ↦ space i.val L) P ∧
    (∀ Q : Finpartition (univ : Finset I), RespectsRelations (fun i : I ↦ space i.val L) Q → P ≤ Q) ∧
    jointMoment L I=∏ C ∈ P.parts, jointMoment L (partImage C) ∧
    centeredCoefficient L I=∏ C ∈ P.parts, centeredCoefficient L (partImage C) ∧
    relativeNullity L I=∑ C ∈ P.parts, relativeNullity L (partImage C) := by
  let S := fun i : I ↦ PaperP1.Arithmetic.squareClassSpace i.val L
  let P := PaperP1.Affine.canonicalRelationPartition S
  have hp : PaperP1.Affine.RelationDirectPartition S P := PaperP1.Affine.canonicalRelationPartition_respects S
  exact ⟨hp,PaperP1.Affine.canonicalRelationPartition_le S,
    PaperP1.UnrestrictedRunComponents.joint_partition L hL I P hp,
    PaperP1.UnrestrictedRunComponents.centered_partition L hL I P hp,
    PaperP1.UnrestrictedRunComponents.nullity_partition L I P hp⟩

theorem expansion_probability_clauses {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace Ω] (G : Finset κ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : κ → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    expansion_centeredMoment μ J ∅=1 ∧
    (∀ x, expansion_centeredMoment μ J {x}=0) ∧
    ∀ I : Finset κ,
      (∀ k, 0≤(∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x)).coeff k) ∧
      expansion_totalMass (∏ x ∈ G \ I, expansion_bernoulli (expansion_marginal μ J x))=1 := by
  refine ⟨PaperP1.Probability.measureCenteredMoment_empty μ J _,
    PaperP1.Probability.measureCenteredMoment_singleton_eq_zero μ J hJ,?_⟩
  intro I
  have h := PaperP1.Probability.measureMarginal_reference_isProbability (G \ I) μ J hJ
  refine ⟨h.1,?_⟩
  rw [expansion_totalMass_eq_source]
  exact h.2

theorem fullSupportLists_eq (G : Finset ℕ) (L r : ℕ) :
    fullSupportLists G L r=PaperP1.FullSupportOrderedLists.manuscriptLists G L r := by rfl

/-- Companion T13.1: one scale threshold precedes all minimum orders and subsets. -/
theorem uniform_full_support_count (C u ε : ℝ) (hu : 0<u) (hε : 0<ε) :
    ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C → ∀ G : Finset ℕ, G⊆Ico N (2*N) →
      ∀ s : ℕ, 2≤s →
      (∑ r ∈ Icc s G.card, (u^r/(r.factorial : ℝ))*
        ((fullSupportLists G L r).card*((2^L : ℝ)⁻¹)^r)) ≤
          (N : ℝ)^(-min ((s : ℝ)/2) 2+ε) := by
  simpa only [fullSupportLists_eq, PaperP1.Model.dyadicBlock] using
    PaperP1.UniformFullSupportCount.companion_T13_1 C u ε hu hε

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
by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_⟩
  · exact expansion_centered_identity
  · exact expansion_probability_clauses
  · exact original_fourier
  · exact finite_envelope
  · exact nominal_envelope
  · exact compatible_nullity
  · exact unique_direct_partition
  · exact canonical_factorization
  · exact uniform_full_support_count

end PaperP1Registry.Final.Affine

namespace PaperP1Registry.Final.Reference

open Finset MeasureTheory
open scoped BigOperators Classical ENNReal

theorem runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω=PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem factorialMoment_eq (N L r : ℕ) :
    factorialMoment N L r=PaperP1.FactorialCountMoments.factorialCountMoment (PaperP1.Model.dyadicBlock N) L r := by rfl

theorem marginal_eq (x L : ℕ) : marginal x L=PaperP1.Model.InfiniteStarts.infiniteMarginal x L := by rfl

theorem jointMoment_eq (L : ℕ) (A : Finset ℕ) :
    jointMoment L A=PaperP1.Model.InfiniteStarts.infiniteJointMoment L A := by rfl

theorem centeredCoefficient_eq (L : ℕ) (A : Finset ℕ) :
    centeredCoefficient L A=PaperP1.Model.InfiniteStarts.infiniteCenteredCoefficient L A := by rfl

theorem third_eq (N L : ℕ) : thirdCumulant N L=
    PaperP1.ThirdRunFactorialCumulant.thirdFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem fourth_eq (N L : ℕ) : fourthCumulant N L=
    PaperP1.FourthRunFactorialCumulant.fourthFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem second_eq (N L : ℕ) : secondCumulant N L=
    PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem principalScale_eq (N L : ℕ) : principalSecondScale N L=
    PaperP1.ChannelMassPhaseEquivalent.phaseMass N L 3 := by
  exact (PaperP1.PrincipalPairPhaseComparison.phase_three N L).symm

theorem factorial_source (N L r : ℕ) :
    Integrable (fun ω ↦ ((runCount N L ω).descFactorial r : ℝ)) primeSignMeasure ∧
    factorialMoment N L r=(r.factorial : ℝ)*
      ∑ A ∈ (Ico N (2*N)).powersetCard r, jointMoment L A :=
by
  constructor
  · exact PaperP1.RetainedMomentTransfer.original_observable_integrable
      (PaperP1.Model.dyadicBlock N) L (fun n : ℕ ↦ (n.descFactorial r : ℝ))
  · simpa only [factorialMoment_eq,jointMoment_eq,PaperP1.Model.dyadicBlock] using
      (PaperP1.FactorialCountMoments.factorialCountMoment_eq_subset
        (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl r)

theorem third_exact_identity (N L : ℕ) :
    thirdCumulant N L=
      6*(∑ A ∈ (Ico N (2*N)).powersetCard 3, centeredCoefficient L A)-
      6*(∑ e ∈ (Ico N (2*N)).powersetCard 2,
        (∑ x ∈ e, marginal x L)*centeredCoefficient L e)+
      2*∑ x ∈ Ico N (2*N), (marginal x L)^3 :=
by
  simpa only [third_eq,centeredCoefficient_eq,marginal_eq,PaperP1.Model.dyadicBlock] using
    (PaperP1.ThirdRunFactorialCumulant.exact_formula
      (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl)

theorem fourth_exact_identity (N L : ℕ) :
    fourthCumulant N L=
      24*(∑ A ∈ (Ico N (2*N)).powersetCard 4, centeredCoefficient L A)-
      12*(∑ e ∈ (Ico N (2*N)).powersetCard 2, centeredCoefficient L e)^2-
      24*(∑ A ∈ (Ico N (2*N)).powersetCard 3,
        centeredCoefficient L A*∑ x ∈ A, marginal x L)+
      24*(∑ e ∈ (Ico N (2*N)).powersetCard 2,
        ((∑ x ∈ e, (marginal x L)^2)+∏ x ∈ e, marginal x L)*centeredCoefficient L e)-
      6*∑ x ∈ Ico N (2*N), (marginal x L)^4 :=
by
  simpa only [fourth_eq,centeredCoefficient_eq,marginal_eq,PaperP1.Model.dyadicBlock] using
    (PaperP1.FourthRunFactorialCumulant.exact_formula
      (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl)

theorem principal_second_equivalent (C τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      0 < principalSecondScale N L ∧ |secondCumulant N L/principalSecondScale N L-1| ≤ τ :=
by
  obtain ⟨N₀,h₀,h⟩ := PaperP1.ActualPairPhase.uniform_phases C τ hτ
  refine ⟨N₀,h₀,?_⟩
  intro N hN L hBand
  obtain ⟨hpos,_hpos4,hrel,_hrel4⟩ := h N hN L hBand
  simpa only [principalScale_eq,second_eq,PaperP1.ActualPairPhase.alpha_eq_cumulant] using
    And.intro hpos hrel

theorem optimal_third_cumulant (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      c*(N : ℝ)^(-41/30 : ℝ) ≤ thirdCumulant N L ∧
        thirdCumulant N L ≤ (N : ℝ)^(-41/30+ε) :=
by
  refine ⟨PaperP1.OptimalThirdCumulant.lowerConstant C,
    PaperP1.OptimalThirdCumulant.lowerConstant_pos C,?_⟩
  intro ε hε
  obtain ⟨N₀,h₀,h⟩ := PaperP1.OptimalThirdCumulant.article_14_1 C ε hε
  refine ⟨N₀,h₀,?_⟩
  intro N hN L hBand
  simpa only [third_eq] using h N hN L hBand

theorem actualMean_eq (N L : ℕ) :
    actualMean N L=PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1 := by rfl

theorem sourceMass_eq (N L k : ℕ) : sourceMass N L k=PaperP1.AtomicProbability.realMass
    (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k := by
  simpa only [sourceMass,runCount_eq,primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure] using
    (PaperP1.RetainedModifiedLaw.realMass_originalLaw (PaperP1.Model.dyadicBlock N) L k).symm

theorem quadraticMass_eq (μ α : ℝ) (k : ℕ) :
    quadraticMass μ α k=PaperP1.PoissonSequence.quadraticMass μ α k := by rfl

theorem error_eq (N L : ℕ) : quadraticError N L=PaperP1.OptimalQuadratic.error N L := by
  simpa only [quadraticError,sourceMass_eq,actualMean_eq,second_eq,quadraticMass_eq,
    PaperP1.OptimalQuadratic.error,PaperP1.OptimalQuadratic.reference] using
    (PaperP1.FourthCharlierLawDistance.distance_eq_sequence
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)
      (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L)
      (by rw [← actualMean_eq]; unfold actualMean moment
          exact integral_nonneg fun ω ↦ pow_nonneg (Nat.cast_nonneg (runCount N L ω)) 1)).symm

theorem signedChannel_eq (L a b : ℕ) : signedChannel L a b=PaperP1.ChannelSumIdentity.signed L a b := by rfl

theorem unsignedChannel_eq (L a b : ℕ) : unsignedChannel L a b=PaperP1.ChannelSumIdentity.unsigned L a b := by rfl

theorem nominalMean_eq (N L : ℕ) : nominalMean N L=PaperP1.FiniteChannelHierarchy.nominalMean N L := by rfl

theorem orientationWeight_eq (a b : ℕ) : orientationWeight a b=PaperP1.FiniteChannelHierarchy.weight a b := by
  exact (PaperP1.FiniteChannelHierarchy.weight_formula a b).symm

theorem heightSum_eq (b L : ℕ) : heightSum b L=PaperP1.FiniteChannelHierarchy.heightSum b L := by
  simp only [heightSum,orientationWeight_eq,signedChannel_eq,PaperP1.FiniteChannelHierarchy.heightSum]
  rfl

theorem coefficient_eq (N L h : ℕ) : coefficient N L h=PaperP1.FiniteChannelHierarchy.coefficient N L h := by
  simp only [coefficient,heightSum_eq,nominalMean_eq,PaperP1.FiniteChannelHierarchy.coefficient,
    PaperP1.FiniteChannelHierarchy.truncatedSum]

theorem twoChannel_eq (N L : ℕ) : twoChannelCoefficient N L=PaperP1.FiniteChannelHierarchy.twoChannelCoefficient N L := by rfl

theorem correction_eq (N L : ℕ) : correction N L=PaperP1.HeightFiveChannelCorrection.correction N L := by
  simp only [correction,heightSum_eq,nominalMean_eq,PaperP1.HeightFiveChannelCorrection.correction]

theorem heightMass_eq (N L b : ℕ) : heightMass N L b=PaperP1.ChannelMassPhaseEquivalent.heightMass N L b := by
  simp only [heightMass,heightSum_eq,nominalMean_eq,PaperP1.ChannelMassPhaseEquivalent.heightMass]

theorem phaseConstant_eq (b r : ℕ) : phaseConstant b r=PaperP1.ChannelPhaseConstants.phaseConstant b r := by rfl

theorem phaseMass_eq (N L b : ℕ) : phaseMass N L b=PaperP1.ChannelMassPhaseEquivalent.phaseMass N L b := by rfl

theorem sourceMeasure_eq (N L : ℕ) : sourceMeasure N L=
    (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L : Measure ℕ) := by
  rw [PaperP1.RetainedModifiedLaw.originalLaw_eq_actual_map]
  unfold sourceMeasure
  rw [show runCount N L=PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L from funext (runCount_eq N L)]
  rfl

theorem sourceSigned_eq (N L : ℕ) : sourceSigned N L=
    (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L : Measure ℕ).toSignedMeasure := by
  exact Measure.toSignedMeasure_congr (sourceMeasure_eq N L)

theorem signedReference_eq (μ α : ℝ) : signedReference μ α=PaperP1.QuadraticPoisson.reference μ α := by rfl

theorem secondDifference_eq (μ : ℝ) : secondDifference μ=
    PaperP1.QuadraticPoisson.differenceMap (PaperP1.QuadraticPoisson.differenceMap (PaperP1.QuadraticPoisson.poissonSigned μ)) := by rfl

theorem distance_eq (ν κ : SignedMeasure ℕ) : distance ν κ=PaperP1.SignedAtomicDistance.distance ν κ := by rfl

theorem secondNorm_eq (μ : ℝ) : secondNorm μ=PaperP1.PoissonDifferenceSigned.norm μ 2 := by rfl

theorem totalVariation_eq (N L : ℕ) (Q : ProbabilityMeasure ℕ) : totalVariation N L Q=
    PaperP1.AtomicProbability.totalVariation (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) Q := by
  rw [totalVariation,sourceMeasure_eq];rfl

theorem leadingGap_eq (N L h : ℕ) : leadingGap N L h=PaperP1.AdjacentReferencePhase.leadingGap N L h := by rfl

theorem hermiteLaw_eq (μ α : ℝ) (hα : 0≤α) (hαμ : α≤μ) :
    hermiteLaw μ α hα hαμ=PaperP1.HermiteReference.law μ α hα hαμ := by rfl

theorem criterion_helper (μ α : ℝ) (hμ : 0 < μ) :
    ((∀ k : ℕ, 0 ≤ quadraticMass μ α k) ∧ HasSum (quadraticMass μ α) 1) ↔
      0 ≤ α ∧ α ≤ 2*μ^2/(μ+fractionalPart μ*(1-fractionalPart μ)) :=
by
  have hSum : HasSum (quadraticMass μ α) 1 := by
    exact PaperP1.PoissonSequence.hasSum_quadraticMass μ α hμ.le
  have hP : (∀ k, 0 ≤ quadraticMass μ α k) ↔
      PaperP1.AtomicSignedLaw.IsProbability (PaperP1.QuadraticPoisson.reference μ α) := by
    simpa only [quadraticMass_eq,PaperP1.QuadraticPoisson.reference] using
      (PaperP1.AtomicSignedLaw.isProbability_ofSequence_iff
        (PaperP1.PoissonSequence.hasSum_quadraticMass μ α hμ.le)).symm
  constructor
  · intro h
    simpa only [fractionalPart,PaperP1.CharlierQuadratic.theta] using
      (PaperP1.QuadraticPoisson.main_8_1 μ α hμ).mp (hP.mp h.1)
  · intro h
    refine ⟨hP.mpr ((PaperP1.QuadraticPoisson.main_8_1 μ α hμ).mpr ?_),hSum⟩
    simpa only [fractionalPart,PaperP1.CharlierQuadratic.theta] using h

theorem quadratic_probability_criterion (μ α : ℝ) (hμ : 0<μ) :
    ((∀ k : ℕ, 0≤quadraticMass μ α k) ∧ HasSum (quadraticMass μ α) 1) ↔
      0≤α ∧ α≤2*μ^2/(μ+fractionalPart μ*(1-fractionalPart μ)) := by
  simpa only [fractionalPart,quadraticMass_eq] using
    criterion_helper μ α hμ

theorem quadratic_mass_formula (μ α : ℝ) (hμ : 0<μ) (k : ℕ) :
    signedReference μ α {k}=Real.exp (-μ)*μ^k/(k.factorial : ℝ)*
      (1+α/(2*μ^2)*(((k : ℝ)-μ)^2-k)) := by
  exact PaperP1.QuadraticPoisson.reference_singleton μ α hμ k

theorem hermite_exact (C ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤secondCumulant N L, ∃ hαμ : secondCumulant N L≤actualMean N L,
      distance (sourceSigned N L)
        (hermiteLaw (actualMean N L) (secondCumulant N L) hα hαμ : Measure ℕ).toSignedMeasure ≤
          (N : ℝ)^(-4/3+ε) ∧
      totalVariation N L (hermiteLaw (actualMean N L) (secondCumulant N L) hα hαμ) ≤
        (N : ℝ)^(-4/3+ε) := by
  simp only [actualMean_eq,second_eq,distance_eq,sourceSigned_eq,totalVariation_eq,hermiteLaw_eq]
  obtain ⟨N₀,hN₀,h⟩ := PaperP1.OptimalHermite.article_19_1_exact C ε hε
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband
  obtain ⟨hα,hαμ,hd,htv⟩ := h N hN L hband
  refine ⟨hα,hαμ,?_,htv⟩
  rwa [PaperP1.HermiteReference.actual_signed_reference _ _ hα hαμ] at hd

theorem hermite_fixed_height (h : ℕ) (hh : 3≤h) (C ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤coefficient N L h, ∃ hαμ : coefficient N L h≤nominalMean N L,
      distance (sourceSigned N L)
        (hermiteLaw (nominalMean N L) (coefficient N L h) hα hαμ : Measure ℕ).toSignedMeasure ≤
          (N : ℝ)^(-1+1/((h+1 : ℕ) : ℝ)+ε) := by
  simp only [coefficient_eq,nominalMean_eq,distance_eq,sourceSigned_eq,hermiteLaw_eq]
  obtain ⟨NB,_hNB,hb⟩ := PaperP1.ExplicitHermiteLaw.uniform_bound h hh C ε hε
  obtain ⟨NP,_hNP,hp⟩ := PaperP1.ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  refine ⟨max 2 (max NB NP),by omega,?_⟩
  intro N hN L hband
  have hp := hp N (by omega) L hband
  refine ⟨hp.1.le,hp.2.1.le,?_⟩
  have hd := hb N (by omega) L hband
  rwa [PaperP1.HermiteReference.actual_signed_reference _ _ hp.1.le hp.2.1.le] at hd

theorem hermite_fixed_equivalent (h : ℕ) (hh : 3≤h) (C : ℝ) :
    ∀ τ : ℝ, 0<τ → ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤coefficient N L h, ∃ hαμ : coefficient N L h≤nominalMean N L,
      0<leadingGap N L h ∧
      |totalVariation N L (hermiteLaw (nominalMean N L) (coefficient N L h) hα hαμ)/
        (phaseMass N L (h+1)*secondNorm (nominalMean N L)/4)-1| ≤ τ := by
  simp only [coefficient_eq,nominalMean_eq,totalVariation_eq,hermiteLaw_eq,leadingGap_eq,phaseMass_eq,secondNorm_eq]
  intro τ hτ
  obtain ⟨NB,_hNB,hb⟩ := PaperP1.ExplicitHermiteLaw.uniform_probability_equivalent h hh C τ hτ
  obtain ⟨NP,_hNP,hp⟩ := PaperP1.ExplicitReferenceAdmissibility.uniform_probabilities C h hh
  refine ⟨max 2 (max NB NP),by omega,?_⟩
  intro N hN L hband
  have hp := hp N (by omega) L hband
  obtain ⟨H,hH,hpos,he⟩ := hb N (by omega) L hband
  have hEq : H=PaperP1.HermiteReference.law
      (PaperP1.FiniteChannelHierarchy.nominalMean N L)
      (PaperP1.FiniteChannelHierarchy.coefficient N L h) hp.1.le hp.2.1.le := by
    have hMeasure : (H : Measure ℕ)=(PaperP1.HermiteReference.law
        (PaperP1.FiniteChannelHierarchy.nominalMean N L)
        (PaperP1.FiniteChannelHierarchy.coefficient N L h) hp.1.le hp.2.1.le : Measure ℕ) :=
      Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
        (hH.trans (PaperP1.HermiteReference.actual_signed_reference _ _ hp.1.le hp.2.1.le))
    exact Subtype.ext hMeasure
  refine ⟨hp.1.le,hp.2.1.le,hpos,?_⟩
  rw [hEq] at he
  exact he

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
by
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_⟩
  · exact quadratic_probability_criterion
  · exact quadratic_mass_formula
  · exact hermite_exact
  · exact hermite_fixed_height
  · exact hermite_fixed_equivalent

end PaperP1Registry.Final.Reference

namespace PaperP1Registry.Final.Obstruction

open MeasureTheory Filter Asymptotics
open scoped BigOperators Classical Topology

theorem baseMass_eq (a : ℝ) : baseMass a=PaperP1.MomentObstructionMass.qMass a := rfl
theorem epsilon_eq (m : ℕ) (a : ℝ) : epsilon m a=PaperP1.MomentObstructionMass.epsilon m a := rfl
theorem parameter_eq (N : ℕ) : parameter N=PaperP1.MomentObstructionSequence.parameter N := rfl
theorem differenceCoefficient_eq (m k : ℕ) : differenceCoefficient m k=
    ((PaperP1.Probability.forwardDifference : PaperP1.Probability.SignedLaw ℝ)^m).coeff k :=
  (PaperP1.DifferenceCoefficients.forwardDifference_pow_coeff m k).symm
theorem perturbedMass_eq (m : ℕ) (a : ℝ) : perturbedMass m a=PaperP1.MomentObstructionMass.pMass m a := by
  funext k
  simp only [perturbedMass,baseMass_eq,epsilon_eq,differenceCoefficient_eq,PaperP1.MomentObstructionMass.pMass]
theorem base_probability (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) : IsProbabilityMass (baseMass a) := by
  exact ⟨by simpa only [baseMass_eq] using PaperP1.MomentObstructionMass.qMass_nonneg a ha0 (by linarith),
    by simpa only [baseMass_eq] using PaperP1.MomentObstructionMass.hasSum_qMass a⟩
theorem perturb_probability (m : ℕ) (hm : 3≤m) (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) :
    IsProbabilityMass (perturbedMass m a) := by
  exact ⟨by simpa only [perturbedMass_eq] using PaperP1.MomentObstructionMass.pMass_nonneg m a ha0 (by linarith),
    by simpa only [perturbedMass_eq] using PaperP1.MomentObstructionMass.hasSum_pMass m (by omega) a⟩
theorem base_moment (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) (j : ℕ) :
    factorialMoment (baseMass a) j=
      ∫ k : ℕ,(k.descFactorial j : ℝ) ∂(PaperP1.MomentObstructionMass.qLaw a ha0 (by linarith) : Measure ℕ) := by
  simp only [PaperP1.MomentObstructionMass.qLaw,PaperP1.AtomicProbability.ofMass_integral,factorialMoment,baseMass_eq]
theorem perturb_moment (m : ℕ) (hm : 3≤m) (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) (j : ℕ) :
    factorialMoment (perturbedMass m a) j=
      ∫ k : ℕ,(k.descFactorial j : ℝ) ∂(PaperP1.MomentObstructionMass.pLaw m (by omega) a ha0 (by linarith) : Measure ℕ) := by
  simp only [PaperP1.MomentObstructionMass.pLaw,PaperP1.AtomicProbability.ofMass_integral,factorialMoment,perturbedMass_eq]
theorem perturb_exp (m : ℕ) (hm : 3≤m) (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) (t : ℝ) :
    exponentialMoment (perturbedMass m a) t=
      ∫ k : ℕ,Real.exp (t*k) ∂(PaperP1.MomentObstructionMass.pLaw m (by omega) a ha0 (by linarith) : Measure ℕ) := by
  simp only [PaperP1.MomentObstructionMass.pLaw,PaperP1.AtomicProbability.ofMass_integral,exponentialMoment,perturbedMass_eq]
theorem perturb_variation (m : ℕ) (hm : 3≤m) (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) :
    variation (perturbedMass m a) (baseMass a)=
      PaperP1.AtomicProbability.totalVariation
        (PaperP1.MomentObstructionMass.pLaw m (by omega) a ha0 (by linarith))
        (PaperP1.MomentObstructionMass.qLaw a ha0 (by linarith)) := by
  simp only [variation,PaperP1.AtomicProbability.totalVariation,
    PaperP1.MomentObstructionMass.pLaw_real_singleton,PaperP1.MomentObstructionMass.qLaw_real_singleton,
    perturbedMass_eq,baseMass_eq]
theorem factorial_summable (m : ℕ) (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1) (j : ℕ) :
    Summable (fun k ↦ perturbedMass m a k*(k.descFactorial j : ℝ)) := by
  have h := PaperP1.MomentObstructionMoments.hasSum_pMass_weighted m a
    (fun k ↦ (k.descFactorial j : ℝ))
    (PaperP1.MomentObstructionMoments.qMass_factorial_summable a ha0 (by linarith) j).hasSum
  simpa only [perturbedMass_eq] using h.summable
theorem exponential_summable (m : ℕ) (a t : ℝ) :
    Summable (fun k ↦ perturbedMass m a k*Real.exp (t*k)) := by
  have h := PaperP1.MomentObstructionMoments.hasSum_pMass_weighted m a
    (fun k ↦ Real.exp (t*k)) (PaperP1.MomentObstructionMoments.hasSum_qMass_exp a t)
  simpa only [perturbedMass_eq] using h.summable
theorem familyMass_eq (N k : ℕ) : familyMass N k=
    (PaperP1.MomentObstructionSequence.familyLaw N : Measure ℕ).real {k} := by
  by_cases h : PaperP1.MomentObstructionSequence.Valid N
  · have hv : Valid N := h
    simp only [familyMass,ite_eq_left hv,PaperP1.MomentObstructionSequence.familyLaw,dite_eq_left h,
      PaperP1.MomentObstructionMass.pLaw_real_singleton,perturbedMass_eq]
    rfl
  · have hv : ¬Valid N := h
    simp only [familyMass,ite_eq_right hv,PaperP1.MomentObstructionSequence.familyLaw,dite_eq_right h,
      PaperP1.MomentObstructionMass.qLaw_real_singleton,PaperP1.MomentObstructionMass.qMass,
      PaperP1.PoissonSequence.quadraticMass,zero_div,zero_mul,add_zero]
    rfl
theorem referenceMass_eq (N k : ℕ) : referenceMass N k=
    (PaperP1.MomentObstructionSequence.referenceFamily N : Measure ℕ).real {k} := by
  by_cases h : PaperP1.MomentObstructionSequence.Valid N
  · have hv : Valid N := h
    simp only [referenceMass,ite_eq_left hv,PaperP1.MomentObstructionSequence.referenceFamily,dite_eq_left h,
      PaperP1.MomentObstructionMass.qLaw_real_singleton,baseMass_eq]
    rfl
  · have hv : ¬Valid N := h
    simp only [referenceMass,ite_eq_right hv,PaperP1.MomentObstructionSequence.referenceFamily,dite_eq_right h,
      PaperP1.MomentObstructionMass.qLaw_real_singleton,PaperP1.MomentObstructionMass.qMass,
      PaperP1.PoissonSequence.quadraticMass,zero_div,zero_mul,add_zero]
    rfl
theorem familyDistance_eq (N : ℕ) : familyDistance N=PaperP1.MomentObstructionSequence.familyDistance N := by
  simp only [familyDistance,variation,PaperP1.MomentObstructionSequence.familyDistance,
    PaperP1.AtomicProbability.totalVariation,familyMass_eq,referenceMass_eq]
theorem family_probability (N : ℕ) : IsProbabilityMass (familyMass N) ∧ IsProbabilityMass (referenceMass N) := by
  constructor
  · refine ⟨fun k ↦ by rw [familyMass_eq]; exact measureReal_nonneg,?_⟩
    have heq : familyMass N=PaperP1.AtomicProbability.realMass (PaperP1.MomentObstructionSequence.familyLaw N) :=
      funext fun k ↦ familyMass_eq N k
    rw [heq]
    exact PaperP1.AtomicProbability.hasSum_realMass (PaperP1.MomentObstructionSequence.familyLaw N)
  · refine ⟨fun k ↦ by rw [referenceMass_eq]; exact measureReal_nonneg,?_⟩
    have heq : referenceMass N=PaperP1.AtomicProbability.realMass (PaperP1.MomentObstructionSequence.referenceFamily N) :=
      funext fun k ↦ referenceMass_eq N k
    rw [heq]
    exact PaperP1.AtomicProbability.hasSum_realMass (PaperP1.MomentObstructionSequence.referenceFamily N)
theorem family_integral (N : ℕ) (f : ℕ → ℝ) :
    (∑' k, familyMass N k*f k)=∫ k,f k ∂(PaperP1.MomentObstructionSequence.familyLaw N : Measure ℕ) := by
  by_cases h : PaperP1.MomentObstructionSequence.Valid N
  · have hv : Valid N := h
    simp only [familyMass,ite_eq_left hv,PaperP1.MomentObstructionSequence.familyLaw,dite_eq_left h,
      PaperP1.MomentObstructionMass.pLaw,PaperP1.AtomicProbability.ofMass_integral,perturbedMass_eq]
    rfl
  · have hv : ¬Valid N := h
    simp only [familyMass,ite_eq_right hv,PaperP1.MomentObstructionSequence.familyLaw,dite_eq_right h,
      PaperP1.MomentObstructionMass.qLaw,PaperP1.AtomicProbability.ofMass_integral,
      PaperP1.MomentObstructionMass.qMass,PaperP1.PoissonSequence.quadraticMass,zero_div,zero_mul,add_zero]
    rfl


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
by
  refine ⟨?_,family_probability,?_,?_,?_,?_⟩
  · intro m hm a ha0 ha1
    obtain ⟨hp,hmom,htv,hexp⟩ := PaperP1.MomentObstruction.companion_T23_1 m hm a ha0 ha1
    refine ⟨base_probability a ha0 ha1,perturb_probability m hm a ha0 ha1,?_,?_,?_,?_⟩
    · intro k
      simpa only [PaperP1.MomentObstructionMass.qLaw_real_singleton,
        PaperP1.MomentObstructionMass.pLaw_real_singleton,baseMass_eq,perturbedMass_eq] using hp k
    · intro j
      refine ⟨factorial_summable m a ha0 ha1 j,?_,?_⟩
      · simpa only [baseMass_eq] using PaperP1.MomentObstructionMoments.qMass_factorial_summable a ha0 (by linarith) j
      · simpa only [base_moment a ha0 ha1 j,perturb_moment m hm a ha0 ha1 j] using (hmom j).2.2
    · simpa only [perturb_variation m hm a ha0 ha1] using htv
    · intro t _ht
      refine ⟨exponential_summable m a t,?_⟩
      simpa only [perturb_exp m hm a ha0 ha1 t,exponentialBound] using (hexp t).2
  · intro r
    filter_upwards [PaperP1.MomentObstructionSequence.valid_eventually,
      PaperP1.MomentObstructionSequence.fixed_factorial_moments_eventually r] with N hN hm
    have hv : Valid N := hN
    refine ⟨?_,?_⟩
    · simpa only [familyMass,ite_eq_left hv] using factorial_summable (order N) (parameter N) hN.2.1 hN.2.2 r
    · simpa only [factorialMoment,family_integral,parameter_eq] using hm
  · intro t _ht
    filter_upwards [PaperP1.MomentObstructionSequence.valid_eventually,
      PaperP1.MomentObstructionSequence.exponential_bound_eventually t] with N hN hb
    have hv : Valid N := hN
    refine ⟨?_,?_⟩
    · simpa only [familyMass,ite_eq_left hv] using exponential_summable (order N) (parameter N) t
    · simpa only [exponentialMoment,family_integral,exponentialBound] using hb.2
  · simpa only [familyDistance_eq] using PaperP1.MomentObstructionSequence.log_distance_error_isBigO
  · intro γ hγ
    simpa only [familyDistance_eq] using PaperP1.MomentObstructionSequence.distance_exceeds_every_power γ hγ

end PaperP1Registry.Final.Obstruction

