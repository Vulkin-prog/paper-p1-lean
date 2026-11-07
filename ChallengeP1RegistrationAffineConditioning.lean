module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring.Basic

/-! # Finite affine structure, conditioning and dependent expansions

Consolidated components retain their literal models, complete hypotheses and
original proof bodies, relocated into distinct model namespaces. The declaration
map records every original statement and source hash. No mathematical change.
-/

set_option autoImplicit false
@[expose] public noncomputable section

section ComponentAffineSpectra

/-! # Exact finite affine spectra and their canonical factorization
Uniform averages, actual effective-block indicators, individual rates,
full-support relations and the finest relation-respecting partition are
literal Mathlib constructions. Incompatible prescriptions retain their zero
mass. The foundational affine counting and character calculations are adapted
through P1 from Paper C, commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Apache-2.0; exact source attribution is in docs/PAPER_C_REUSE.md.
-/

namespace PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra
open Finset
open scoped Classical BigOperators

abbrev F₂ := ZMod 2
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The literal normalized uniform average over a finite carrier. -/
def average {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  ∑ v, (Fintype.card V : ℝ)⁻¹*f v

def solutionMass {V W : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]
    [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) : ℝ :=
  average fun v ↦ if A v=b then 1 else 0

def character {V : Type*} [AddCommGroup V] [Module F₂ V]
    (f : V →ₗ[F₂] F₂) (v : V) : ℝ := if f v=0 then 1 else -1

/-- One effective block's actual affine event, with a local compatible target. -/
def indicator {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) (a v : V) : ℝ :=
  if ∀ s : S, s.val v=s.val a then 1 else 0

def rate {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) [Fintype S] : ℝ :=
  (Fintype.card S : ℝ)⁻¹

/-- Addition from the product of the actual effective spaces. -/
def addition {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : ((i : ι) → S i) →ₗ[F₂] U where
  toFun := fun s ↦ ∑ i, (s i).val
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.smul_sum]

def relativeNullity {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : ℕ := Module.finrank F₂ (LinearMap.ker (addition S))

def FullRelation {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) (s : (i : ι) → S i) : Prop :=
  (∀ i, s i ≠ 0) ∧ addition S s=0

/-- Every relation remains a relation after restriction to any part. -/
def RespectsRelations {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U)
    (P : Finpartition (univ : Finset ι)) : Prop :=
  ∀ s : (i : ι) → S i, addition S s=0 →
    ∀ C ∈ P.parts, ∑ i ∈ C, (s i).val=0

def tupleSign {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) (s : (i : ι) → S i) : ℝ :=
  ∏ i, character (s i).val (a i)

def jointMoment {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) : ℝ :=
  average fun v ↦ ∏ i, indicator (S i) (a i) v

def centeredMoment {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) : ℝ :=
  average fun v ↦ ∏ i, (indicator (S i) (a i) v-rate (S i))

/-- Exact mass and positivity of every finite affine system, including all
incompatible systems, using the effective image rank. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_uniform_affine_mass {V W : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) :
    solutionMass A b=(if b ∈ LinearMap.range A then
      ((2 : ℝ)^(Module.finrank F₂ (LinearMap.range A)))⁻¹ else 0) ∧
    (0<solutionMass A b ↔ b ∈ LinearMap.range A) :=
by sorry

/-- Actual individual marginal rates and the exact centered full-support
Fourier sum, retaining every affine sign and heterogeneous block dimension. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_centered_fourier_formula {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    (∀ i, average (fun v ↦ indicator (S i) (a i) v)=rate (S i) ∧
      rate (S i)=((2 : ℝ)^(Module.finrank F₂ (S i)))⁻¹ ∧ 0<rate (S i)) ∧
    centeredMoment S a=(∏ i, rate (S i))*
      ∑ s : (i : ι) → S i, if FullRelation S s then tupleSign S a s else 0 :=
by sorry

/-- Exact dimension deficit, the sharper 2^rho-1 centered bound, and a
full-support relation whenever the centered moment is nonzero. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_sharp_relative_nullity_bound {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    relativeNullity S=(∑ i, Module.finrank F₂ (S i))-
      Module.finrank F₂ (⨆ i, S i : Submodule F₂ (V →ₗ[F₂] F₂)) ∧
    |centeredMoment S a| ≤ (∏ i, rate (S i))*((2 : ℝ)^(relativeNullity S)-1) ∧
    (centeredMoment S a ≠ 0 → ∃ s : (i : ι) → S i, FullRelation S s) :=
by sorry

/-- The unique finest relation-respecting partition factors both actual
ordinary and centered moments and adds their effective relative nullities. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_canonical_factorization {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] :
    ∃! P : Finpartition (univ : Finset ι),
      RespectsRelations S P ∧
      (∀ Q, RespectsRelations S Q → P ≤ Q) ∧
      (∀ a : ι → V,
        jointMoment S a=∏ C : P.parts,
          jointMoment (fun i : C.val ↦ S i.val) (fun i ↦ a i.val) ∧
        centeredMoment S a=∏ C : P.parts,
          centeredMoment (fun i : C.val ↦ S i.val) (fun i ↦ a i.val)) ∧
      relativeNullity S=∑ C : P.parts, relativeNullity (fun i : C.val ↦ S i.val) :=
by sorry

end PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra

end ComponentAffineSpectra

section ComponentConditioning

/-! # Actual conditional laws and colored replica target sums
The independent prime-sign law, literal run bits, joint probabilities and
shared-small-prime colored replicas are explicit. All thresholds precede the
moving scales and all source prescriptions. The source count remains fixed.
Selected model foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the four selected Challenge theorem holes are deliberate placeholders.
-/

namespace PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning
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

/-- A start has the opposite preceding sign and a constant following word.
Both signs are counted; the boundary condition prevents counting interior shifts. -/
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x-1)+g x=1 ∧ ∀ j : ℕ, j<L → g (x+j)=g x

def startIndicator (x L : ℕ) (ω : Sample) : Bool := decide (StartEvent (valueBit ω) x L)

/-- Number of actual run starts in the complete dyadic block [N,2N). -/
def runCount (N L : ℕ) (ω : Sample) : ℕ :=
  ∑ x ∈ Ico N (2*N), (startIndicator x L ω).toNat

/-- Actual relative window bits; row zero is the preceding boundary equation. -/
def startBits (x L : ℕ) (ω : Sample) (i : Fin L) : F₂ :=
  if i.val=0 then valueBit ω (x-1)+valueBit ω x else valueBit ω x+valueBit ω (x+i.val)

def sourceEvent {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂) (ω : Sample) : Prop :=
  ∀ i, startBits (x i) L ω=b i

/-- Literal conditional probability, with the actual joint mass denominator. -/
def conditionalProbability {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂)
    (z : ℕ) (c : Fin L → F₂) : ℝ :=
  primeSignMeasure.real {ω | sourceEvent x L b ω ∧ startBits z L ω=c}/
    primeSignMeasure.real {ω | sourceEvent x L b ω}

def jointStarts (A : Finset ℕ) (L : ℕ) : Set Sample :=
  {ω | ∀ x ∈ A, StartEvent (valueBit ω) x L}

def jointMass (A : Finset ℕ) (L : ℕ) : ℝ := primeSignMeasure.real (jointStarts A L)

def conditionalStart (A : Finset ℕ) (L z : ℕ) : ℝ := jointMass (insert z A) L/jointMass A L

def negativeDeviation (N L : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ z ∈ Ico N (2*N) \ A, max 0 ((2^L : ℝ)⁻¹-conditionalStart A L z)

/-- One common sign sample and independently colored fresh samples. -/
abbrev ColoredSample (κ : Type*) := Sample × (κ → Sample)

def coloredMeasure (κ : Type*) [Fintype κ] : Measure (ColoredSample κ) :=
  primeSignMeasure.prod (Measure.pi (fun _ : κ ↦ primeSignMeasure))

instance coloredProbability (κ : Type*) [Fintype κ] : IsProbabilityMeasure (coloredMeasure κ) := by
  unfold coloredMeasure
  infer_instance

/-- All primes at most Y use the common sample; larger primes use the indicated color. -/
def selected {κ : Type*} (Y : ℕ) (k : κ) (ω : ColoredSample κ) : Sample :=
  fun j ↦ if Nat.nth Nat.Prime j ≤ Y then ω.1 j else ω.2 k j

def coloredBits {κ : Type*} (Y x L : ℕ) (k : κ) (ω : ColoredSample κ) : Fin L → F₂ :=
  startBits x L (selected Y k ω)

def coloredSourceEvent {κ : Type*} {s : ℕ} (Y L : ℕ) (x : Fin s → ℕ)
    (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂) (ω : ColoredSample κ) : Prop :=
  ∀ i, coloredBits Y (x i) L (color (some i)) ω=b i

def coloredConditionalProbability {κ : Type*} [Fintype κ] {s : ℕ} (Y L : ℕ)
    (x : Fin s → ℕ) (z : ℕ) (color : Option (Fin s) → κ)
    (b : Fin s → Fin L → F₂) (c : Fin L → F₂) : ℝ :=
  (coloredMeasure κ).real {ω | coloredSourceEvent Y L x color b ω ∧ coloredBits Y z L (color none) ω=c}/
    (coloredMeasure κ).real {ω | coloredSourceEvent Y L x color b ω}

/-- Uniform conditional target sum for all compatible source prescriptions
and arbitrary target prescriptions, even depending on the target centre. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.conditioning_conditional_target_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2*N)) →
      ∀ b : Fin s → Fin L → F₂,
        0 < primeSignMeasure.real {ω | sourceEvent x L b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2*N), conditionalProbability x L b z (c z)) ≤ (N : ℝ)^ε :=
by sorry

/-- The same cutoff works for every finite replica color set, every shared
small-prime cutoff and every color assignment, after conditioning on the actual
positive joint source probability. The number of sources s remains fixed. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.conditioning_colored_target_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2*N)) →
      ∀ (κ : Type*) [Fintype κ], ∀ Y : ℕ, ∀ color : Option (Fin s) → κ,
      ∀ b : Fin s → Fin L → F₂,
        0 < (coloredMeasure κ).real {ω | coloredSourceEvent Y L x color b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2*N), coloredConditionalProbability Y L x z color b (c z)) ≤ (N : ℝ)^ε :=
by sorry

/-- Actual negative conditional deviation after any fixed number of starts.
All source sets and every positive actual joint conditioning event are uniform. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.conditioning_negative_deviation (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ Ico N (2*N) → A.card ≤ j → 0 < jointMass A L →
      negativeDeviation N L A ≤ (N : ℝ)^(-1/2+ε) :=
by sorry

/-- Conditional mean of the literal full count after removing the prescribed
source starts, with its actual probability denominator retained. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.conditioning_conditional_mean_lower (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ Ico N (2*N) → A.card ≤ j → 0 < jointMass A L →
      (N : ℝ)*(2^L : ℝ)⁻¹-(N : ℝ)^(-1/2+ε) ≤
        (∫ ω, if ω ∈ jointStarts A L then (runCount N L ω : ℝ)-(A.card : ℝ) else 0 ∂primeSignMeasure)/
          jointMass A L :=
by sorry

end PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning

end ComponentConditioning

section ComponentDependentExpansion

/-! # Exact expansions for dependent indicator counts
Every source count, probability and heterogeneous centered moment is literal.
The ordered boundary deletes the greatest element of its prefix. The positive
kernel keeps the actual dependent suffix and is charged only in ordinary l1.
No independence or approximation assumption is imposed.
-/

namespace PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion
open Finset MeasureTheory
open scoped Classical BigOperators

variable {ι Ω : Type*}

/-- Prefix with the greatest element removed, also defined on the empty set. -/
def properPrefix [LinearOrder ι] (I : Finset ι) : Finset ι :=
  I.filter fun x ↦ ∃ y ∈ I, x<y

def Hereditary (D : Finset ι → Prop) : Prop :=
  ∀ ⦃I J⦄, J ⊆ I → D I → D J

def Boundary [LinearOrder ι] (D : Finset ι → Prop) (I : Finset ι) : Prop :=
  ¬ D I ∧ D (properPrefix I)

def suffix [LinearOrder ι] (G I : Finset ι) : Finset ι :=
  G.filter fun y ↦ ∀ x ∈ I, x<y

def retained (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter D

def boundary [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) : Finset (Finset ι) :=
  G.powerset.filter (Boundary D)

abbrev SignedLaw := AddMonoidAlgebra ℝ ℕ

def scalar (r : ℝ) : SignedLaw := AddMonoidAlgebra.single 0 r

def atom (k : ℕ) : SignedLaw := AddMonoidAlgebra.single k 1

def difference : SignedLaw := atom 1-atom 0

def bernoulli (p : ℝ) : SignedLaw := atom 0+scalar p*difference

/-- Ordinary unweighted singleton l1 norm. -/
def l1Norm (ν : SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ |r|

def totalMass (ν : SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ r

def indicator (b : Bool) : ℝ := if b then 1 else 0

def count (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat

/-- All count probabilities, represented on their literal finite support. -/
def countLaw [MeasurableSpace Ω] (G : Finset ι) (μ : Measure Ω)
    (J : ι → Ω → Bool) : SignedLaw :=
  ∑ k ∈ range (G.card+1), AddMonoidAlgebra.single k (μ.real {ω | count G J ω=k})

def jointMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ := ∫ ω, ∏ x ∈ I, indicator (J x ω) ∂μ

def marginal [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool) (x : ι) : ℝ :=
  ∫ ω, indicator (J x ω) ∂μ

def centeredMoment [MeasurableSpace Ω] (μ : Measure Ω) (J : ι → Ω → Bool)
    (I : Finset ι) : ℝ :=
  ∫ ω, ∏ x ∈ I, (indicator (J x ω)-marginal μ J x) ∂μ

/-- A signed reference of mass one, whose coefficients need not be positive. -/
def retainedReference [MeasurableSpace Ω] (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : SignedLaw :=
  ∑ I ∈ retained G D, scalar (jointMoment μ J I)*difference^I.card

/-- Exact first-excluded-prefix identity, already over a commutative semiring. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_polynomial_expansion {R : Type*} [LinearOrder ι] [CommSemiring R]
    (G : Finset ι) (D : Finset ι → Prop) (u : ι → R) (t : R)
    (hD : Hereditary D) (h0 : D ∅) :
    (∏ x ∈ G, (1+t*u x))=
      (∑ I ∈ retained G D, t^I.card*∏ x ∈ I, u x)+
      ∑ I ∈ boundary G D, (t^I.card*∏ x ∈ I, u x)*
        ∏ y ∈ suffix G I, (1+t*u y) :=
by sorry

/-- The exact actual law, with heterogeneous marginals and arbitrary dependence.
Its coefficients are the original count probabilities and it is normalized. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_centered_identity [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    (∀ k, (countLaw G μ J).coeff k=μ.real {ω | count G J ω=k}) ∧
    (∀ k, 0 ≤ (countLaw G μ J).coeff k) ∧ totalMass (countLaw G μ J)=1 ∧
    countLaw G μ J=∑ I ∈ G.powerset, scalar (centeredMoment μ J I)*
      difference^I.card*∏ x ∈ G \ I, bernoulli (marginal μ J x) :=
by sorry

/-- Each positive kernel has the actual prefix/suffix joint expectation as
its coefficients and exactly the prefix activation probability as mass/norm.
The suffix is allowed to depend on the entire prefix. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_positive_stopped_kernel [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : Hereditary D) (h0 : D ∅) :
    totalMass (retainedReference G D μ J)=1 ∧
    ∃ K : Finset ι → SignedLaw,
      countLaw G μ J-retainedReference G D μ J=
        ∑ I ∈ boundary G D, difference^I.card*K I ∧
      (∀ I k, (K I).coeff k=∫ ω, (∏ x ∈ I, indicator (J x ω))*
        (if count (suffix G I) J ω=k then 1 else 0) ∂μ) ∧
      ∀ I, (∀ k, 0 ≤ (K I).coeff k) ∧
        totalMass (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} ∧
        l1Norm (K I)=μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by sorry

/-- Ordinary l1 error depends only on the ordered boundary activity mass;
there is no factor charging the number of dependent suffix indicators. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_stopped_l1_bound [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : Hereditary D) (h0 : D ∅) :
    l1Norm (countLaw G μ J-retainedReference G D μ J) ≤
      ∑ I ∈ boundary G D, (2 : ℝ)^I.card*μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by sorry

end PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion

end ComponentDependentExpansion
