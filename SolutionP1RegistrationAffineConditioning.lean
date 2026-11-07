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
public import PaperP1.Affine.PartitionMoments
public import PaperP1.Affine.PartitionNullity
public import PaperP1.Asymptotics.ConditionalNegativeDeviation
public import PaperP1.Asymptotics.FixedSourceConditionalSum
public import PaperP1.Asymptotics.InfiniteColoredConditionalSum
public import PaperP1.Probability.StoppedMeasureLaw

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


theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.average_eq_source {V : Type*} [Fintype V] [Nonempty V] (f : V → ℝ) :
    average f=PaperP1.Algebra.finiteExpectation
      (PaperP1.Probability.uniformFiniteProbability V).weight f := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.solutionMass_eq_source {V W : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) :
    solutionMass A b=PaperP1.Affine.uniformSolutionMass A b := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.character_eq_source {V : Type*} [AddCommGroup V] [Module F₂ V]
    (f : V →ₗ[F₂] F₂) (v : V) : character f v=PaperP1.Affine.realCharacter f v := by
  by_cases h : f v=0 <;> simp [character,PaperP1.Affine.realCharacter,PaperP1.Affine.binarySign,h]

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.indicator_eq_source {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) (a v : V) :
    indicator S a v=PaperP1.Affine.effectiveIndicator S a v := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.rate_eq_source {V : Type*} [AddCommGroup V] [Module F₂ V]
    (S : Submodule F₂ (V →ₗ[F₂] F₂)) [Fintype S] :
    rate S=PaperP1.Affine.effectiveRate S := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.addition_eq_source {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : addition S=PaperP1.Affine.relationAddition S := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.relativeNullity_eq_source {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) : relativeNullity S=PaperP1.Affine.relativeNullity S := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.fullRelation_iff_source {U ι : Type*} [AddCommGroup U] [Module F₂ U] [Fintype ι]
    (S : ι → Submodule F₂ U) (s : (i : ι) → S i) :
    FullRelation S s ↔ PaperP1.Affine.IsFullSupportRelation S s := Iff.rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.respectsRelations_iff_source {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U)
    (P : Finpartition (univ : Finset ι)) :
    RespectsRelations S P ↔ PaperP1.Affine.RelationDirectPartition S P := Iff.rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.tupleSign_eq_source {V ι : Type*} [AddCommGroup V] [Module F₂ V] [Fintype ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) (s : (i : ι) → S i) :
    tupleSign S a s=PaperP1.Affine.affineTupleSign S a s := by
  simp only [tupleSign,PaperP1.Affine.affineTupleSign,character_eq_source]

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.jointMoment_eq_source {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) (a : ι → V) :
    jointMoment S a=PaperP1.Affine.effectiveJointMoment S a := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.AffineSpectra.centeredMoment_eq_source {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    centeredMoment S a=PaperP1.Affine.effectiveCenteredMoment S a := rfl

/-- Exact mass and positivity of every finite affine system, including all
incompatible systems, using the effective image rank. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_uniform_affine_mass {V W : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [AddCommGroup W] [Module F₂ W] (A : V →ₗ[F₂] W) (b : W) :
    solutionMass A b=(if b ∈ LinearMap.range A then
      ((2 : ℝ)^(Module.finrank F₂ (LinearMap.range A)))⁻¹ else 0) ∧
    (0<solutionMass A b ↔ b ∈ LinearMap.range A) :=
by
  rw [solutionMass_eq_source]
  constructor
  · by_cases h : b ∈ LinearMap.range A
    · rw [ite_eq_left h]
      exact PaperP1.Affine.uniformSolutionMass_of_compatible A b h
    · rw [ite_eq_right h]
      exact PaperP1.Affine.uniformSolutionMass_of_not_compatible A b h
  · exact PaperP1.Affine.uniformSolutionMass_pos_iff A b

/-- Actual individual marginal rates and the exact centered full-support
Fourier sum, retaining every affine sign and heterogeneous block dimension. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_centered_fourier_formula {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    (∀ i, average (fun v ↦ indicator (S i) (a i) v)=rate (S i) ∧
      rate (S i)=((2 : ℝ)^(Module.finrank F₂ (S i)))⁻¹ ∧ 0<rate (S i)) ∧
    centeredMoment S a=(∏ i, rate (S i))*
      ∑ s : (i : ι) → S i, if FullRelation S s then tupleSign S a s else 0 :=
by
  constructor
  · intro i
    refine ⟨?_,?_,?_⟩
    · exact PaperP1.Affine.effective_marginal (S i) (a i)
    · have hcard : Fintype.card (S i)=2^(Module.finrank F₂ (S i)) :=
        PaperP1.Affine.card_eq_two_pow_finrank (V := S i)
      simp only [rate,hcard,Nat.cast_pow,Nat.cast_ofNat]
    · exact inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := S i)))
  · simpa only [centeredMoment_eq_source,PaperP1.Affine.effectiveCenteredMoment,rate_eq_source,fullRelation_iff_source,
      tupleSign_eq_source] using PaperP1.Affine.effective_full_support_formula S a

/-- Exact dimension deficit, the sharper 2^rho-1 centered bound, and a
full-support relation whenever the centered moment is nonzero. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.affine_spectra_sharp_relative_nullity_bound {V ι : Type*} [AddCommGroup V] [Module F₂ V]
    [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (S : ι → Submodule F₂ (V →ₗ[F₂] F₂)) [∀ i, Fintype (S i)] (a : ι → V) :
    relativeNullity S=(∑ i, Module.finrank F₂ (S i))-
      Module.finrank F₂ (⨆ i, S i : Submodule F₂ (V →ₗ[F₂] F₂)) ∧
    |centeredMoment S a| ≤ (∏ i, rate (S i))*((2 : ℝ)^(relativeNullity S)-1) ∧
    (centeredMoment S a ≠ 0 → ∃ s : (i : ι) → S i, FullRelation S s) :=
by
  refine ⟨PaperP1.Affine.relativeNullity_eq_dimension_deficit S,
    PaperP1.Affine.effectiveCenteredMoment_bound S a,?_⟩
  exact PaperP1.Affine.fullSupportRelation_of_centeredMoment_ne_zero S a

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
by
  obtain ⟨P,⟨hP,hfinest⟩,hunique⟩ := PaperP1.Affine.existsUnique_finest_relationPartition S
  refine ⟨P,⟨hP,hfinest,?_,?_⟩,?_⟩
  · intro a
    exact ⟨PaperP1.Affine.effectiveJointMoment_partition S P hP a,
      PaperP1.Affine.effectiveCenteredMoment_partition S P hP a⟩
  · exact PaperP1.Affine.relativeNullity_partition_additive S P hP
  · intro Q hQ
    exact hunique Q ⟨hQ.1,hQ.2.1⟩

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

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.measure_eq : primeSignMeasure = PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.bits_eq (x L : ℕ) (ω : Sample) :
    startBits x L ω=PaperP1.RelativeSignIndependence.infiniteStartBits x L ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.conditional_eq {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂)
    (z : ℕ) (c : Fin L → F₂) :
    conditionalProbability x L b z c=PaperP1.WindowFamilyConditional.conditionalProbability x L b z c := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.jointStarts_eq (A : Finset ℕ) (L : ℕ) : jointStarts A L=PaperP1.JointBranchingEvents.jointEvent A L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.jointMass_eq (A : Finset ℕ) {L : ℕ} (hL : 0 < L) :
    jointMass A L=PaperP1.Model.InfiniteStarts.infiniteJointMoment L A := by
  exact (PaperP1.JointBranchingEvents.infiniteJointMoment_eq_probability A hL).symm

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.negative_eq (N : ℕ) {L : ℕ} (hL : 0 < L) (A : Finset ℕ) :
    negativeDeviation N L A=PaperP1.SourceConditionalDeviations.negativeDeviation N L A := by
  simp only [negativeDeviation,conditionalStart,jointMass_eq _ hL]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω=PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.coloredMeasure_eq (κ : Type*) [Fintype κ] :
    coloredMeasure κ=PaperP1.InfiniteColoredSamples.measure κ := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.Conditioning.coloredConditional_eq {κ : Type*} [Fintype κ] {s : ℕ} (Y L : ℕ)
    (x : Fin s → ℕ) (z : ℕ) (color : Option (Fin s) → κ)
    (b : Fin s → Fin L → F₂) (c : Fin L → F₂) :
    coloredConditionalProbability Y L x z color b c=
      PaperP1.InfiniteColoredConditional.conditionalProbability Y L x z color b c := by rfl

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
by
  obtain ⟨N₀,h⟩ := PaperP1.FixedSourceConditionalSum.conditional_sum s hs C ε hε
  refine ⟨N₀,?_⟩
  intro N hN L hBand x hx b hb c
  simpa only [conditional_eq] using h N hN L hBand x hx b hb c

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
by
  obtain ⟨N₀,h⟩ := PaperP1.InfiniteColoredConditionalSum.companion_T22_7 s hs C ε hε
  refine ⟨N₀,?_⟩
  intro N hN L hBand x hx κ _ Y color b hb c
  simpa only [coloredConditional_eq] using h N hN L hBand x hx κ Y color b hb c

/-- Actual negative conditional deviation after any fixed number of starts.
All source sets and every positive actual joint conditioning event are uniform. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.conditioning_negative_deviation (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ Ico N (2*N) → A.card ≤ j → 0 < jointMass A L →
      negativeDeviation N L A ≤ (N : ℝ)^(-1/2+ε) :=
by
  obtain ⟨N₀,h₀,h⟩ := PaperP1.ConditionalNegativeDeviation.uniform_negative C j ε hε
  obtain ⟨NG,hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max N₀ NG,by omega,?_⟩
  intro N hN L hBand A hA hCard hMass
  have hL : 0 < L := by have hh := (hG N (by omega) L hBand).2.2.1; omega
  rw [negative_eq N hL A]
  apply h N (by omega) L hBand A hA hCard
  rwa [←jointMass_eq A hL]

/-- Conditional mean of the literal full count after removing the prescribed
source starts, with its actual probability denominator retained. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.conditioning_conditional_mean_lower (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ Ico N (2*N) → A.card ≤ j → 0 < jointMass A L →
      (N : ℝ)*(2^L : ℝ)⁻¹-(N : ℝ)^(-1/2+ε) ≤
        (∫ ω, if ω ∈ jointStarts A L then (runCount N L ω : ℝ)-(A.card : ℝ) else 0 ∂primeSignMeasure)/
          jointMass A L :=
by
  obtain ⟨N₀,h₀,h⟩ := PaperP1.ConditionalNegativeDeviation.uniform_conditional_expectation_lower C j ε hε
  obtain ⟨NG,hG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max N₀ NG,by omega,?_⟩
  intro N hN L hBand A hA hCard hMass
  have hL : 0 < L := by have hh := (hG N (by omega) L hBand).2.2.1; omega
  have hPos : 0 < PaperP1.Model.InfiniteStarts.infiniteJointMoment L A := by
    rwa [←jointMass_eq A hL]
  simpa only [PaperP1.FiniteChannelHierarchy.nominalMean,runCount_eq,measure_eq,jointMass,jointStarts_eq] using
    h N (by omega) L hBand A hA hCard hPos

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


/-- Finite reconstruction uses the literal coefficient sequence. -/
theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.reconstruct (ν : SignedLaw) (n : ℕ)
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

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.countLaw_eq_source [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    countLaw G μ J=PaperP1.Probability.observedCountLaw G μ J hJ := by
  have h := reconstruct (PaperP1.Probability.observedCountLaw G μ J hJ) G.card
    (fun k hk ↦ PaperP1.Probability.countLaw_coeff_eq_zero_of_card_lt G
      (PaperP1.Probability.indicatorObservationProbability μ J hJ).weight
      (fun x σ ↦ σ x) hk)
  rw [h]
  unfold countLaw
  apply Finset.sum_congr rfl
  intro k _
  rw [PaperP1.Probability.observedCountLaw_coeff]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.totalMass_eq_source (ν : SignedLaw) :
    totalMass ν=PaperP1.Probability.totalMass ν :=
  (PaperP1.Probability.totalMass_eq_sum_coeff ν).symm

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.l1Norm_eq_source (ν : SignedLaw) :
    l1Norm ν=PaperP1.Probability.l1Norm ν := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.retainedReference_eq_source [MeasurableSpace Ω]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω)
    (J : ι → Ω → Bool) :
    retainedReference G D μ J=PaperP1.Probability.measureRetainedReference G D μ J := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.jointMoment_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    jointMoment μ J I=PaperP1.Probability.measureJointMoment μ J I := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.marginal_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (x : ι) :
    marginal μ J x=PaperP1.Probability.measureMarginal μ J x := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.centeredMoment_eq_source [MeasurableSpace Ω] (μ : Measure Ω)
    (J : ι → Ω → Bool) (I : Finset ι) :
    centeredMoment μ J I=PaperP1.Probability.measureCenteredMoment μ J
      (PaperP1.Probability.measureMarginal μ J) I := rfl

theorem _root_.PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion.boundary_eq_source [LinearOrder ι] (G : Finset ι) (D : Finset ι → Prop) :
    boundary G D=PaperP1.Algebra.boundarySets G D := rfl

/-- Exact first-excluded-prefix identity, already over a commutative semiring. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_polynomial_expansion {R : Type*} [LinearOrder ι] [CommSemiring R]
    (G : Finset ι) (D : Finset ι → Prop) (u : ι → R) (t : R)
    (hD : Hereditary D) (h0 : D ∅) :
    (∏ x ∈ G, (1+t*u x))=
      (∑ I ∈ retained G D, t^I.card*∏ x ∈ I, u x)+
      ∑ I ∈ boundary G D, (t^I.card*∏ x ∈ I, u x)*
        ∏ y ∈ suffix G I, (1+t*u y) :=
by
  exact PaperP1.Algebra.stopped_expansion G D u t hD h0

/-- The exact actual law, with heterogeneous marginals and arbitrary dependence.
Its coefficients are the original count probabilities and it is normalized. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_centered_identity [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x)) :
    (∀ k, (countLaw G μ J).coeff k=μ.real {ω | count G J ω=k}) ∧
    (∀ k, 0 ≤ (countLaw G μ J).coeff k) ∧ totalMass (countLaw G μ J)=1 ∧
    countLaw G μ J=∑ I ∈ G.powerset, scalar (centeredMoment μ J I)*
      difference^I.card*∏ x ∈ G \ I, bernoulli (marginal μ J x) :=
by
  rw [countLaw_eq_source G μ J hJ]
  have hp := PaperP1.Probability.observedCountLaw_isProbability G μ J hJ
  refine ⟨?_,hp.1,?_,?_⟩
  · intro k
    exact PaperP1.Probability.observedCountLaw_coeff G μ J hJ k
  · rw [totalMass_eq_source]
    exact hp.2
  · exact PaperP1.Probability.centered_measure_expansion G μ J hJ

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
by
  constructor
  · rw [totalMass_eq_source,retainedReference_eq_source]
    exact PaperP1.Probability.measureRetainedReference_mass G D μ J hJ h0
  · refine ⟨PaperP1.Probability.measureBoundaryKernel G μ J hJ,?_,?_,?_⟩
    · rw [countLaw_eq_source G μ J hJ,retainedReference_eq_source]
      exact PaperP1.Probability.stopped_measure_count_difference G D μ J hJ hD h0
    · intro I k
      exact PaperP1.Probability.measureBoundaryKernel_coeff G μ J hJ I k
    · intro I
      refine ⟨PaperP1.Probability.measureBoundaryKernel_nonneg G μ J hJ I,?_,?_⟩
      · rw [totalMass_eq_source,PaperP1.Probability.measureBoundaryKernel_mass,
          PaperP1.Probability.measureJointMoment_eq_probability μ J hJ]
      · rw [l1Norm_eq_source,PaperP1.Probability.measureBoundaryKernel_l1Norm,
          PaperP1.Probability.measureJointMoment_eq_probability μ J hJ]

/-- Ordinary l1 error depends only on the ordered boundary activity mass;
there is no factor charging the number of dependent suffix indicators. -/
theorem _root_.PaperP1Registry.Registration.AffineConditioning.dependent_expansion_stopped_l1_bound [MeasurableSpace Ω] [Fintype ι] [LinearOrder ι]
    (G : Finset ι) (D : Finset ι → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ι → Ω → Bool) (hJ : ∀ x, Measurable (J x))
    (hD : Hereditary D) (h0 : D ∅) :
    l1Norm (countLaw G μ J-retainedReference G D μ J) ≤
      ∑ I ∈ boundary G D, (2 : ℝ)^I.card*μ.real {ω | ∀ x ∈ I, J x ω=true} :=
by
  rw [l1Norm_eq_source,countLaw_eq_source G μ J hJ,retainedReference_eq_source,boundary_eq_source]
  simpa only [PaperP1.Probability.measureJointMoment_eq_probability μ J hJ] using
    PaperP1.Probability.stopped_measure_count_l1_bound G D μ J hJ hD h0

end PaperP1Registry.RegistrationModels.AffineConditioning.DependentExpansion

end ComponentDependentExpansion
