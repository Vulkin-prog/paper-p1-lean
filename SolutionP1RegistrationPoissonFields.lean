module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic.NormNum
public import PaperP1.Asymptotics.ExactPoissonScale
public import PaperP1.Asymptotics.IndependentPositionalApproximation
public import PaperP1.Asymptotics.OptimalNominalQuadratic
public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Model.RetainedMomentTransfer
public import PaperP1.Probability.PositionalBlockIndependence

/-! # Poisson approximation, scales and positional reference fields

Consolidated components retain their literal models, complete hypotheses and
original proof bodies, relocated into distinct model namespaces. The declaration
map records every original statement and source hash. No mathematical change.
-/

set_option autoImplicit false
@[expose] public noncomputable section

section ComponentQuadraticApproximation

/-! # Optimal quadratic approximation of actual multiplicative-run counts

The random prime signs, literal run starts, actual mean and second factorial
cumulant, Poisson singleton masses and full l1 error are all defined below
using Mathlib. The finite and infinite model foundations are adapted through
P1 from Paper C, exact commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Apache-2.0; source identities and adaptations are in docs/PAPER_C_REUSE.md.
The four Challenge statement holes are deliberate selections, not proofs.
-/

namespace PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation
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

/-- Actual moments under the prime-sign law. -/
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure

def actualMean (N L : ℕ) : ℝ := moment N L 1

/-- The second factorial cumulant, with every actual marginal retained. -/
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2

/-- Actual singleton probabilities of the complete count law. -/
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}

def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹

/-- Poisson singleton mass at a real parameter; only nonnegative means are used. -/
def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)

/-- Shift by one, with zero mass below zero. -/
def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k

/-- The exact quadratic Poisson--Charlier reference, Pi_mu+(alpha/2)Delta^2 Pi_mu. -/
def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)

/-- Ordinary singleton l1 distance. Absolute summability is proved explicitly. -/
def quadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω = PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.runCount_fun_eq (N L : ℕ) : runCount N L =
    PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L :=
  funext (runCount_eq N L)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.moment_eq (N L j : ℕ) :
    moment N L j = PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L j := by
  simp only [moment,runCount_eq,PaperP1.CountObservables.countMoment,
    primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.actualMean_eq (N L : ℕ) :
    actualMean N L = PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1 :=
  moment_eq N L 1

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.cumulant_eq (N L : ℕ) :
    secondCumulant N L = PaperP1.RegularCumulantTransfer.secondFactorialCumulant
      (PaperP1.Model.dyadicBlock N) L := by
  simp only [secondCumulant,actualMean_eq,moment_eq,
    PaperP1.RegularCumulantTransfer.secondFactorialCumulant]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.sourceMass_eq (N L k : ℕ) :
    sourceMass N L k = PaperP1.AtomicProbability.realMass
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k := by
  simpa only [sourceMass,runCount_eq,primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure] using
    (PaperP1.RetainedModifiedLaw.realMass_originalLaw (PaperP1.Model.dyadicBlock N) L k).symm

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.sourceMass_fun_eq (N L : ℕ) : sourceMass N L = PaperP1.AtomicProbability.realMass
    (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) :=
  funext (sourceMass_eq N L)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.mean_nonneg (N L : ℕ) : 0 ≤ actualMean N L := by
  unfold actualMean moment
  exact integral_nonneg fun ω ↦ pow_nonneg (Nat.cast_nonneg (runCount N L ω)) 1

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.quadraticMass_eq (μ α : ℝ) (k : ℕ) :
    quadraticMass μ α k = PaperP1.PoissonSequence.quadraticMass μ α k := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.quadraticMass_fun_eq (μ α : ℝ) : quadraticMass μ α =
    PaperP1.PoissonSequence.quadraticMass μ α := funext (quadraticMass_eq μ α)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation.error_eq (N L : ℕ) : quadraticError N L = PaperP1.OptimalQuadratic.error N L := by
  simpa only [quadraticError,sourceMass_eq,quadraticMass_eq,actualMean_eq,cumulant_eq,
    PaperP1.OptimalQuadratic.error,PaperP1.OptimalQuadratic.reference] using
    (PaperP1.FourthCharlierLawDistance.distance_eq_sequence
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)
      (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L)
      (by simpa only [actualMean_eq] using mean_nonneg N L)).symm

/-- Measurability, all finite moments, and normalization of the literal source. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.quadratic_approximation_source_probability (N L : ℕ) :
    Measurable (runCount N L) ∧
    (∀ j : ℕ, Integrable (fun ω ↦ (runCount N L ω : ℝ)^j) primeSignMeasure) ∧
    (∀ k : ℕ, 0 ≤ sourceMass N L k) ∧ HasSum (sourceMass N L) 1 :=
by
  refine ⟨?_,?_,fun k ↦ measureReal_nonneg,?_⟩
  · simpa only [runCount_fun_eq] using
      PaperP1.Model.InfiniteStarts.measurable_infiniteStartCount (PaperP1.Model.dyadicBlock N) L
  · intro j
    simpa only [runCount_eq,primeSignMeasure,coordinateMeasure,
      PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
      PaperP1.Model.InfiniteRademacher.coordinateMeasure] using
      PaperP1.RetainedMomentTransfer.original_observable_integrable
        (PaperP1.Model.dyadicBlock N) L (fun k ↦ (k : ℝ)^j)
  · simpa only [sourceMass_fun_eq] using
      PaperP1.AtomicProbability.hasSum_realMass
        (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)

/-- The reference is normalized as a signed sequence at every scale, and the
error series is absolutely summable. The l1 error is therefore not a totalized
value of an undefined infinite sum. Eventual positivity is part of the main theorem. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.quadratic_approximation_reference_series (N L : ℕ) :
    HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 ∧
    Summable (fun k : ℕ ↦ |sourceMass N L k-
      quadraticMass (actualMean N L) (secondCumulant N L) k|) :=
by
  have hSum : HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 := by
    simpa only [quadraticMass_fun_eq] using
      PaperP1.PoissonSequence.hasSum_quadraticMass (actualMean N L) (secondCumulant N L) (mean_nonneg N L)
  exact ⟨hSum,((_root_.PaperP1Registry.Registration.PoissonFields.quadratic_approximation_source_probability N L).2.2.2.summable.sub hSum.summable).abs⟩

/-- Complete article theorem 1.1: optimal upper and lower powers, exact mean
and second factorial cumulant, quantified nominal-mean bias, and a genuine
probability reference. A single threshold precedes every critical word length. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.quadratic_approximation_optimal_quadratic (C ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      a*(N : ℝ)^(-4/3-ε) ≤ quadraticError N L ∧
      quadraticError N L ≤ (N : ℝ)^(-4/3+ε) ∧
      |actualMean N L-nominalMean N L| ≤ (2 : ℝ)^C*(N : ℝ)^(-1+ε) ∧
      (∀ k : ℕ, 0 ≤ quadraticMass (actualMean N L) (secondCumulant N L) k) ∧
      HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 :=
by
  obtain ⟨a,ha,N₀,h₀,h⟩ := PaperP1.OptimalQuadratic.article_1_1 C ε hε
  refine ⟨a,ha,N₀,h₀,?_⟩
  intro N hN L hBand
  obtain ⟨hl,hu,hBias,hProbability⟩ := h N hN L hBand
  have hSum := (_root_.PaperP1Registry.Registration.PoissonFields.quadratic_approximation_reference_series N L).1
  have hNonneg : ∀ k, 0 ≤ quadraticMass (actualMean N L) (secondCumulant N L) k := by
    have hOriginal : PaperP1.AtomicSignedLaw.IsProbability
        (PaperP1.QuadraticPoisson.reference (actualMean N L) (secondCumulant N L)) := by
      simpa only [actualMean_eq,cumulant_eq,PaperP1.OptimalQuadratic.reference] using hProbability
    have hh := (PaperP1.AtomicSignedLaw.isProbability_ofSequence_iff
      (PaperP1.PoissonSequence.hasSum_quadraticMass (actualMean N L) (secondCumulant N L)
        (mean_nonneg N L))).mp hOriginal
    simpa only [quadraticMass_fun_eq] using hh
  refine ⟨?_,?_,?_,hNonneg,hSum⟩
  · simpa only [error_eq] using hl
  · simpa only [error_eq] using hu
  · simpa only [actualMean_eq,nominalMean] using hBias

/-- Fractional part on the nonnegative mean domain used by the next theorem. -/
def fractionalMean (μ : ℝ) : ℝ := μ-(⌊μ⌋₊ : ℝ)

/-- Exact admissibility interval for the quadratic Poisson reference, including
both coefficient endpoints. All masses and the sum-one condition are explicit. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.quadratic_approximation_probability_criterion (μ α : ℝ) (hμ : 0 < μ) :
    ((∀ k : ℕ, 0 ≤ quadraticMass μ α k) ∧ HasSum (quadraticMass μ α) 1) ↔
      0 ≤ α ∧ α ≤ 2*μ^2/(μ+fractionalMean μ*(1-fractionalMean μ)) :=
by
  have hSum : HasSum (quadraticMass μ α) 1 := by
    simpa only [quadraticMass_fun_eq] using PaperP1.PoissonSequence.hasSum_quadraticMass μ α hμ.le
  have hP : (∀ k, 0 ≤ quadraticMass μ α k) ↔
      PaperP1.AtomicSignedLaw.IsProbability (PaperP1.QuadraticPoisson.reference μ α) := by
    simpa only [quadraticMass_eq,PaperP1.QuadraticPoisson.reference] using
      (PaperP1.AtomicSignedLaw.isProbability_ofSequence_iff
        (PaperP1.PoissonSequence.hasSum_quadraticMass μ α hμ.le)).symm
  constructor
  · intro h
    simpa only [fractionalMean,PaperP1.CharlierQuadratic.theta] using
      (PaperP1.QuadraticPoisson.main_8_1 μ α hμ).mp (hP.mp h.1)
  · intro h
    refine ⟨hP.mpr ((PaperP1.QuadraticPoisson.main_8_1 μ α hμ).mpr ?_),hSum⟩
    simpa only [fractionalMean,PaperP1.CharlierQuadratic.theta] using h

end PaperP1Registry.RegistrationModels.PoissonFields.QuadraticApproximation

end ComponentQuadraticApproximation

section ComponentPoissonScales

/-! # Exact Poisson scales and quantized mean bias for multiplicative runs

The independent prime-sign model and actual count masses are explicit. The
two Poisson means have a common moving residue-dependent equivalent; changing
the mean of the quadratic reference has a separate quantized cost. The latter
comparison applies on biased scales and asserts no infinitude of such scales.
The model foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the five selected Challenge theorem holes are deliberate placeholders.
-/

namespace PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales
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

/-- Actual moments under the prime-sign law. -/
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure

def actualMean (N L : ℕ) : ℝ := moment N L 1

/-- The second factorial cumulant, with every actual marginal retained. -/
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2

/-- Actual singleton probabilities of the complete count law. -/
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}

def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹

/-- Poisson singleton mass at a real parameter; only nonnegative means are used. -/
def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)

/-- Shift by one, with zero mass below zero. -/
def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k

/-- The exact quadratic Poisson--Charlier reference, Pi_mu+(alpha/2)Delta^2 Pi_mu. -/
def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)

/-- Actual total variation from the Poisson law at the actual mean. -/
def actualPoissonTV (N L : ℕ) : ℝ :=
  (∑' k : ℕ, |sourceMass N L k-poissonMass (actualMean N L) k|)/2

/-- Actual total variation from the Poisson law at the nominal mean N/2^L. -/
def nominalPoissonTV (N L : ℕ) : ℝ :=
  (∑' k : ℕ, |sourceMass N L k-poissonMass (nominalMean N L) k|)/2

/-- The literal second finite difference of Poisson singleton masses. -/
def secondDifferenceMass (μ : ℝ) (k : ℕ) : ℝ :=
  shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k

/-- The singleton l1 norm of the actual second Poisson difference. -/
def secondNorm (μ : ℝ) : ℝ := ∑' k : ℕ, |secondDifferenceMass μ k|

/-- The moving residue-class scale, with its literal nominal Poisson mean. -/
def phaseScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(72*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*secondNorm (nominalMean N L)*L*(N : ℝ)^(-2/3 : ℝ)

/-- The quadratic reference after changing only its mean to N/2^L.
The exact second factorial cumulant is held fixed. -/
def nominalQuadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (nominalMean N L) (secondCumulant N L) k|

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω = PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.runCount_fun_eq (N L : ℕ) : runCount N L =
    PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L :=
  funext (runCount_eq N L)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.moment_eq (N L j : ℕ) :
    moment N L j = PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L j := by
  simp only [moment,runCount_eq,PaperP1.CountObservables.countMoment,
    primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.actualMean_eq (N L : ℕ) :
    actualMean N L = PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1 :=
  moment_eq N L 1

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.cumulant_eq (N L : ℕ) :
    secondCumulant N L = PaperP1.RegularCumulantTransfer.secondFactorialCumulant
      (PaperP1.Model.dyadicBlock N) L := by
  simp only [secondCumulant,actualMean_eq,moment_eq,
    PaperP1.RegularCumulantTransfer.secondFactorialCumulant]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.sourceMass_eq (N L k : ℕ) :
    sourceMass N L k = PaperP1.AtomicProbability.realMass
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k := by
  simpa only [sourceMass,runCount_eq,primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure] using
    (PaperP1.RetainedModifiedLaw.realMass_originalLaw (PaperP1.Model.dyadicBlock N) L k).symm

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.sourceMass_fun_eq (N L : ℕ) : sourceMass N L = PaperP1.AtomicProbability.realMass
    (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) :=
  funext (sourceMass_eq N L)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.mean_nonneg (N L : ℕ) : 0 ≤ actualMean N L := by
  unfold actualMean moment
  exact integral_nonneg fun ω ↦ pow_nonneg (Nat.cast_nonneg (runCount N L ω)) 1

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.quadraticMass_eq (μ α : ℝ) (k : ℕ) :
    quadraticMass μ α k = PaperP1.PoissonSequence.quadraticMass μ α k := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.quadraticMass_fun_eq (μ α : ℝ) : quadraticMass μ α =
    PaperP1.PoissonSequence.quadraticMass μ α := funext (quadraticMass_eq μ α)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.nominalMean_eq (N L : ℕ) : nominalMean N L = PaperP1.FiniteChannelHierarchy.nominalMean N L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.nominal_nonneg (N L : ℕ) : 0 ≤ nominalMean N L := by
  unfold nominalMean
  positivity

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.poissonLaw_realMass (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    PaperP1.AtomicProbability.realMass (PaperP1.QuadraticPoisson.poissonLaw μ hμ) k = poissonMass μ k := by
  exact ProbabilityTheory.poissonMeasure_real_singleton ⟨μ,hμ⟩ k

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.actualTV_eq (N L : ℕ) : actualPoissonTV N L = PaperP1.ExactPoissonScale.actualTV N L := by
  unfold actualPoissonTV PaperP1.ExactPoissonScale.actualTV PaperP1.AtomicProbability.totalVariation
  congr 1
  apply tsum_congr
  intro k
  change |sourceMass N L k-poissonMass (actualMean N L) k| =
    |PaperP1.AtomicProbability.realMass (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k-
      PaperP1.AtomicProbability.realMass (PaperP1.ExactPoissonScale.actualPoisson N L) k|
  rw [sourceMass_eq,PaperP1.ExactPoissonScale.actualPoisson,poissonLaw_realMass,actualMean_eq]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.nominalTV_eq (N L : ℕ) : nominalPoissonTV N L = PaperP1.ExactPoissonScale.nominalTV N L := by
  unfold nominalPoissonTV PaperP1.ExactPoissonScale.nominalTV PaperP1.AtomicProbability.totalVariation
  congr 1
  apply tsum_congr
  intro k
  change |sourceMass N L k-poissonMass (nominalMean N L) k| =
    |PaperP1.AtomicProbability.realMass (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k-
      PaperP1.AtomicProbability.realMass (PaperP1.ExactPoissonScale.nominalPoisson N L) k|
  rw [sourceMass_eq,PaperP1.ExactPoissonScale.nominalPoisson,poissonLaw_realMass,nominalMean_eq]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.difference_two (a : ℕ → ℝ) :
    PaperP1.FiniteShiftAction.difference 2 a = PaperP1.PoissonSequence.secondDifference a := by
  have hShift : PaperP1.PoissonSequence.shift (PaperP1.PoissonSequence.shift a-a) =
      PaperP1.PoissonSequence.shift (PaperP1.PoissonSequence.shift a)-PaperP1.PoissonSequence.shift a :=
    map_sub PaperP1.FiniteShiftAction.shiftLinear _ _
  simp only [PaperP1.FiniteShiftAction.difference_succ,PaperP1.FiniteShiftAction.difference_zero]
  rw [hShift]
  funext k
  simp only [PaperP1.PoissonSequence.secondDifference,Pi.sub_apply]
  ring

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.secondNorm_eq (μ : ℝ) (hμ : 0 ≤ μ) : secondNorm μ = PaperP1.PoissonDifferenceSigned.norm μ 2 := by
  rw [PaperP1.PoissonDifferenceSigned.norm_eq_l1 μ hμ 2]
  unfold secondNorm PaperP1.IteratedPoissonDifferences.l1
  rw [difference_two]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.phaseScale_eq (N L : ℕ) : phaseScale N L = PaperP1.ExactPoissonScale.phaseScale N L := by
  unfold phaseScale
  rw [secondNorm_eq _ (nominal_nonneg N L),nominalMean_eq]
  exact (PaperP1.ExactPoissonScale.phaseScale_formula N L).symm

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales.nominal_error_eq (N L : ℕ) :
    nominalQuadraticError N L = PaperP1.OptimalNominalQuadratic.nominalError N L := by
  simpa only [nominalQuadraticError,sourceMass_eq,quadraticMass_eq,nominalMean_eq,cumulant_eq,
    PaperP1.OptimalNominalQuadratic.nominalError] using
    (PaperP1.FourthCharlierLawDistance.distance_eq_sequence
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)
      (PaperP1.FiniteChannelHierarchy.nominalMean N L)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L)
      (by simpa only [nominalMean_eq] using nominal_nonneg N L)).symm

/-- Measurability, all finite moments and normalization of the literal source. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_scales_source_probability (N L : ℕ) :
    Measurable (runCount N L) ∧
    (∀ j : ℕ, Integrable (fun ω ↦ (runCount N L ω : ℝ)^j) primeSignMeasure) ∧
    (∀ k : ℕ, 0 ≤ sourceMass N L k) ∧ HasSum (sourceMass N L) 1 :=
by
  refine ⟨?_,?_,fun k ↦ measureReal_nonneg,?_⟩
  · simpa only [runCount_fun_eq] using
      PaperP1.Model.InfiniteStarts.measurable_infiniteStartCount (PaperP1.Model.dyadicBlock N) L
  · intro j
    simpa only [runCount_eq,primeSignMeasure,coordinateMeasure,
      PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
      PaperP1.Model.InfiniteRademacher.coordinateMeasure] using
      PaperP1.RetainedMomentTransfer.original_observable_integrable
        (PaperP1.Model.dyadicBlock N) L (fun k ↦ (k : ℝ)^j)
  · simpa only [sourceMass_fun_eq] using
      PaperP1.AtomicProbability.hasSum_realMass
        (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)

/-- Complete first-order Poisson comparisons for both means, retaining the
actual second factorial cumulant and their distinct error powers. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_scales_poisson_expansion (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      |actualPoissonTV N L-secondCumulant N L/4*secondNorm (actualMean N L)| ≤
        (N : ℝ)^(-4/3+ε) ∧
      |nominalPoissonTV N L-secondCumulant N L/4*secondNorm (nominalMean N L)| ≤
        (N : ℝ)^(-1+ε) :=
by
  obtain ⟨N₀,h₀,h⟩ := (PaperP1.ExactPoissonScale.article_1_2 C ε hε).1
  refine ⟨N₀,h₀,?_⟩
  intro N hN L hBand
  have hA : secondNorm (actualMean N L) = PaperP1.PoissonDifferenceSigned.norm
      (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1) 2 := by
    rw [secondNorm_eq _ (mean_nonneg N L),actualMean_eq]
  have hB : secondNorm (nominalMean N L) = PaperP1.PoissonDifferenceSigned.norm
      (PaperP1.FiniteChannelHierarchy.nominalMean N L) 2 := by
    rw [secondNorm_eq _ (nominal_nonneg N L),nominalMean_eq]
  simpa only [actualTV_eq,nominalTV_eq,cumulant_eq,hA,hB] using h N hN L hBand

/-- Both actual total variations have the same moving residue-dependent
equivalent, whose denominator uses the nominal mean. One cutoff precedes
all scales and all critical lengths for each relative tolerance. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_scales_moving_residue_equivalent (C : ℝ) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      0 < phaseScale N L ∧ |nominalPoissonTV N L/phaseScale N L-1| ≤ τ ∧
        |actualPoissonTV N L/phaseScale N L-1| ≤ τ :=
by
  intro τ hτ
  obtain ⟨N₀,h₀,h⟩ := (PaperP1.ExactPoissonScale.article_1_2 C 1 (by norm_num)).2 τ hτ
  refine ⟨N₀,h₀,?_⟩
  intro N hN L hBand
  simpa only [phaseScale_eq,actualTV_eq,nominalTV_eq] using h N hN L hBand

/-- The actual mean bias is an integer multiple of the word probability.
Consequently every nonzero bias is at least one such quantum. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_scales_mean_bias_quantized (N L : ℕ) (hN : 2 ≤ N) (hL : 0 < L) :
    ∃ b : ℤ, actualMean N L-nominalMean N L = (2^L : ℝ)⁻¹*(b : ℝ) ∧
      (actualMean N L=nominalMean N L ∨
        (2^L : ℝ)⁻¹ ≤ |actualMean N L-nominalMean N L|) :=
by
  obtain ⟨hi,hd⟩ := (PaperP1.OptimalNominalQuadratic.article_17_3 0 1 (by norm_num)).1 N L hN hL
  refine ⟨PaperP1.MeanBiasQuantization.bias (PaperP1.Model.dyadicBlock N) L,?_,?_⟩
  · simpa only [actualMean_eq,nominalMean_eq] using hi
  · simpa only [actualMean_eq,nominalMean_eq,PaperP1.OptimalNominalQuadratic.meanGap] using hd

/-- Replacing the exact mean in the quadratic reference has error of the
same order as each nonzero actual mean gap, with the exact cumulant fixed.
This does not assert that biased scales occur infinitely often. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_scales_nominal_quadratic_comparison (C ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      nominalQuadraticError N L ≤ (N : ℝ)^(-1+ε) ∧
      (actualMean N L≠nominalMean N L →
        c*|actualMean N L-nominalMean N L| ≤ nominalQuadraticError N L ∧
        nominalQuadraticError N L ≤ (6+c)*|actualMean N L-nominalMean N L|) :=
by
  obtain ⟨N₀,h₀,h⟩ := PaperP1.OptimalNominalQuadratic.uniform_comparison C ε hε
  obtain ⟨NG,hGeometry⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨PaperP1.OptimalNominalQuadratic.lowerConstant C,
    PaperP1.OptimalNominalQuadratic.lowerConstant_pos C,max N₀ NG,by omega,?_⟩
  intro N hN L hBand
  have hN2 : 2 ≤ N := by omega
  have hL : 0 < L := by
    have hh := (hGeometry N (by omega) L hBand).2.2.1
    omega
  obtain ⟨hu,hc⟩ := h N (by omega) L hBand
  refine ⟨?_,?_⟩
  · simpa only [nominal_error_eq] using hu
  · intro hGap
    have hBias : PaperP1.MeanBiasQuantization.bias (PaperP1.Model.dyadicBlock N) L ≠ 0 := by
      intro hz
      have hi := PaperP1.MeanBiasQuantization.main_17_3_integer_identity hN2 hL
      rw [hz,Int.cast_zero,mul_zero] at hi
      apply hGap
      simpa only [actualMean_eq,nominalMean] using sub_eq_zero.mp hi
    simpa only [nominal_error_eq,actualMean_eq,nominalMean_eq,
      PaperP1.OptimalNominalQuadratic.meanGap] using hc hBias

end PaperP1Registry.RegistrationModels.PoissonFields.PoissonScales

end ComponentPoissonScales

section ComponentPositionalField

/-! # The original weighted positional field and its independent Poisson arrivals

The arithmetic good edges, individual joint probabilities, nominal single rates,
original grid and every fixed polynomial weight are literal Mathlib-only data.
Prime-sign and start foundations are adapted through P1 from Paper C commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the three selected Challenge statement holes are deliberate placeholders.
-/

namespace PaperP1Registry.RegistrationModels.PoissonFields.PositionalField
open Finset MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal

local instance positionalDecidable (P : Prop) : Decidable P := Classical.propDecidable P

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


/-- The complete original dyadic grid. -/
def ground (N : ℕ) : Finset ℕ := Ico N (2*N)

/-- The actual joint start probability, as the integral of its indicator. -/
def jointRate (L : ℕ) (I : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ I, (if startIndicator x L ω then (1 : ℝ) else 0) ∂primeSignMeasure

/-- The predecessor and the following L original vertices. -/
def vertexLabel (x L : ℕ) (v : Fin (L+1)) : ℕ :=
  if v.val=0 then x-1 else x+(v.val-1)

def vertexParityMap (x L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun v ↦ parity (vertexLabel x L v))

/-- Zero total parity selects an even number of window vertices. -/
def evennessMap (L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] F₂ where
  toFun w := ∑ v, w v
  map_add' w z := by simp only [Pi.add_apply,Finset.sum_add_distrib]
  map_smul' c w := by
    change (∑ v, c*w v)=c*∑ v,w v
    rw [Finset.mul_sum]

def evenParityMap (x L : ℕ) : LinearMap.ker (evennessMap L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (vertexParityMap x L).comp (LinearMap.ker (evennessMap L)).subtype

/-- Effective even square classes, with actual local relations factored out. -/
def squareClassSpace (x L : ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  LinearMap.range (evenParityMap x L)

def windowValues (x L : ℕ) : Finset ℕ := univ.image (vertexLabel x L)

def normalizedWindow (c x L : ℕ) : Finset ℕ :=
  (windowValues x L).image (fun n ↦ c*n)

def normalizedUnion (a b x y L : ℕ) : Finset ℕ :=
  normalizedWindow b x L ∪ normalizedWindow a y L

/-- Every normalized value has a prime above H private to that value. -/
def PrivateAbove (H : ℝ) (S : Finset ℕ) : Prop :=
  ∀ n∈S, ∃ p : ℕ, Nat.Prime p ∧ H<(p : ℝ) ∧ parity n p≠0 ∧
    ∀ m∈S,m≠n → parity m p=0

def Leading (a b : ℕ) : Prop := (a=2 ∧ b=3) ∨ (a=3 ∧ b=4)

/-- The original arithmetic good-edge predicate, including dependence. -/
def GoodEdge (H : ℝ) (N L x y : ℕ) : Prop :=
  x∈ground N ∧ y∈ground N ∧ x<y ∧ 0<jointRate L {x,y} ∧
    ¬Disjoint (squareClassSpace x L) (squareClassSpace y L) ∧
      ∃ a b : ℕ, Leading a b ∧ PrivateAbove H (normalizedUnion a b x y L)

def goodEdges (H : ℝ) (N L : ℕ) : Finset (Finset ℕ) :=
  (((ground N) ×ˢ (ground N)).filter (fun xy ↦ GoodEdge H N L xy.1 xy.2)).image
    (fun xy ↦ ({xy.1,xy.2} : Finset ℕ))

/-- The actual total pair intensity incident to one original site. -/
def incidence (H : ℝ) (N L x : ℕ) : ℝ :=
  ∑ e ∈ goodEdges H N L, if x∈e then jointRate L e else 0

abbrev Channel (N L : ℕ) :=
  ↥(ground N) ⊕ ↥(goodEdges (8*(L+1) : ℕ) N L)

/-- Nonnegative rates are bundled only after their arithmetic positivity proof. -/
def arrivalRate (N L : ℕ)
    (hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x) :
    Channel N L → ℝ≥0
  | Sum.inl x => ⟨(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x.val,hp x.val x.property⟩
  | Sum.inr e => ⟨jointRate L e.val,by
      apply integral_nonneg
      intro ω
      exact prod_nonneg fun x _ ↦ by split <;> norm_num⟩

/-- Independent single-site and pair arrivals on a concrete product space. -/
def arrivalMeasure (N L : ℕ)
    (hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x) :
    Measure (Channel N L → ℕ) := Measure.pi (fun a ↦ poissonMeasure (arrivalRate N L hp a))

/-- Each original site receives its own arrival and the incident pair arrivals. -/
def field (N L : ℕ) (ω : Channel N L → ℕ) (x : ground N) : ℕ :=
  ω (Sum.inl x)+∑ e : goodEdges (8*(L+1) : ℕ) N L,
    if x.val∈e.val then ω (Sum.inr e) else 0

/-- The actual unsigned field on the literal original grid. -/
def sourceMass (N L : ℕ) (z : ground N → ℕ) : ℝ :=
  primeSignMeasure.real {ω | ∀ x : ground N, (startIndicator x.val L ω).toNat=z x}


theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.jointRate_nonneg (L : ℕ) (I : Finset ℕ) : 0 ≤ jointRate L I := by
  apply integral_nonneg
  intro ω
  exact prod_nonneg fun x _ ↦ by split <;> norm_num

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.jointRate_eq (L : ℕ) (I : Finset ℕ) :
    jointRate L I=PaperP1.Model.InfiniteStarts.infiniteJointMoment L I := rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.squareClassSpace_eq (x L : ℕ) :
    squareClassSpace x L=PaperP1.Arithmetic.squareClassSpace x L := rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.goodEdges_eq (H : ℝ) (N L : ℕ) :
    goodEdges H N L=PaperP1.GoodEdgeCompression.goodEdges H N L := rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.incidence_eq (H : ℝ) (N L x : ℕ) :
    incidence H N L x=PaperP1.PositionalCompoundPoisson.incidence
      (PaperP1.GoodEdgeCompression.goodEdges H N L)
      (PaperP1.Model.InfiniteStarts.infiniteJointMoment L) x := by
  unfold incidence PaperP1.PositionalCompoundPoisson.incidence
  rw [goodEdges_eq]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hx : x∈e
  · simp only [hx,ite_true,jointRate_eq]
  · simp only [hx,ite_false]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.arrivalRate_eq (N L : ℕ)
    (hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x)
    (hp' : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-
      PaperP1.PositionalCompoundPoisson.incidence (goodEdges (8*(L+1) : ℕ) N L) (jointRate L) x)
    (a : Channel N L) :
    arrivalRate N L hp a=PaperP1.PositionalPoissonRealization.channelRate (ground N)
      (goodEdges (8*(L+1) : ℕ) N L) (fun _ ↦ (2^L : ℝ)⁻¹) (jointRate L)
      hp' (fun e _ ↦ jointRate_nonneg L e) a := by
  cases a with
  | inl x =>
    apply Subtype.ext
    change (2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x.val = _
    rw [incidence_eq]
    rfl
  | inr e => rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.field_eq (N L : ℕ) (ω : Channel N L → ℕ) (x : ground N) :
    field N L ω x=(∑ a : Channel N L, ω a •
      PaperP1.PositionalPoissonRealization.channelJump (ground N)
        (goodEdges (8*(L+1) : ℕ) N L) a) x.val := by
  rw [PaperP1.PositionalPoissonRealization.field_coordinate]
  unfold field
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hx : x.val∈e.val
  · simp only [hx,ite_true]
  · simp only [hx,ite_false]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.sourceMass_eq (N L : ℕ) (z : ground N → ℕ) :
    sourceMass N L z=PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure.real
      {ω | ∀ x : ground N, (PaperP1.Model.InfiniteStarts.infiniteStartIndicator x.val L ω).toNat=z x} := rfl


theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PositionalField.arrivalMeasure_eq (N L : ℕ)
    (hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x)
    (hp' : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-
      PaperP1.PositionalCompoundPoisson.incidence (goodEdges (8*(L+1) : ℕ) N L) (jointRate L) x) :
    arrivalMeasure N L hp=(PaperP1.PositionalPoissonRealization.poissonProduct
      (PaperP1.PositionalPoissonRealization.channelRate (ground N)
        (goodEdges (8*(L+1) : ℕ) N L) (fun _ ↦ (2^L : ℝ)⁻¹) (jointRate L)
        hp' (fun e _ ↦ jointRate_nonneg L e))).val := by
  unfold arrivalMeasure PaperP1.PositionalPoissonRealization.poissonProduct
  congr 1
  funext a
  rw [arrivalRate_eq N L hp hp' a]

/-- Original arithmetic single rates are positive uniformly over every cutoff. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.positional_field_positive_single_rates (C : ℝ) :
    ∃ N₀ : ℕ, 3≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C → ∀ H : ℝ, ∀ x : ℕ,
      0<(2^L : ℝ)⁻¹-incidence H N L x := by
  simpa only [incidence_eq] using PaperP1.WeakPairIncidence.full_single_rates_positive C

/-- The full original weighted grid law for every independent Poisson realization. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.positional_field_weighted_original_grid (C ε : ℝ) (hε : 0<ε) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C →
      ∃ hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x,
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Channel N L → Ω → ℕ),
        (∀ a, HasLaw (X a) (poissonMeasure (arrivalRate N L hp a)) P) → iIndepFun X P →
        let error := fun z : ground N → ℕ ↦ (1+∑ x : ground N,(z x : ℝ))^j *
          |sourceMass N L z-P.real {ω | ∀ x : ground N,field N L (fun a ↦ X a ω) x=z x}|
        Summable error ∧ (∑' z : ground N → ℕ,error z)≤(N : ℝ)^(-4/5+ε) := by
  intro j
  obtain ⟨N₀,hN₀,h⟩ := PaperP1.IndependentPositionalApproximation.main_20_1 C ε hε j
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband
  obtain ⟨hp',hh⟩ := h N hN L hband
  let hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x := by
    intro x hx
    rw [incidence_eq]
    exact hp' x hx
  refine ⟨hp,?_⟩
  intro Ω _ P _ X hX hInd
  have hX' (a : Channel N L) : HasLaw (X a)
      (poissonMeasure (PaperP1.PositionalPoissonRealization.channelRate (ground N)
        (goodEdges (8*(L+1) : ℕ) N L) (fun _ ↦ (2^L : ℝ)⁻¹) (jointRate L)
        hp' (fun e _ ↦ jointRate_nonneg L e) a)) P := by
    rw [← arrivalRate_eq N L hp hp' a]
    exact hX a
  have hbound := hh Ω P X hX' hInd
  simp_rw [sourceMass_eq,field_eq]
  convert hbound using 1
  · apply summable_congr
    intro z
    congr 1
  · apply iff_of_eq
    congr 1

/-- The same convergent comparison on the explicit product Poisson space. -/
theorem _root_.PaperP1Registry.Registration.PoissonFields.positional_field_canonical_weighted_grid (C ε : ℝ) (hε : 0<ε) :
    ∀ j : ℕ, ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2|≤C →
      ∃ hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x,
      let error := fun z : ground N → ℕ ↦ (1+∑ x : ground N,(z x : ℝ))^j *
        |sourceMass N L z-(arrivalMeasure N L hp).real
          {ω | ∀ x : ground N,field N L ω x=z x}|
      Summable error ∧ (∑' z : ground N → ℕ,error z)≤(N : ℝ)^(-4/5+ε) := by
  intro j
  obtain ⟨N₀,hN₀,h⟩ := PaperP1.IndependentPositionalApproximation.main_20_1_canonical C ε hε j
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband
  obtain ⟨hp',hbound⟩ := h N hN L hband
  let hp : ∀ x∈ground N, 0≤(2^L : ℝ)⁻¹-incidence (8*(L+1) : ℕ) N L x := by
    intro x hx
    rw [incidence_eq]
    exact hp' x hx
  refine ⟨hp,?_⟩
  simp_rw [sourceMass_eq,arrivalMeasure_eq N L hp hp',field_eq]
  convert hbound using 1
  · apply summable_congr
    intro z
    congr 1
  · apply iff_of_eq
    congr 1

end PaperP1Registry.RegistrationModels.PoissonFields.PositionalField

end ComponentPositionalField

section ComponentPoissonReference

/-! # Exact probability structure of the compensated Poisson reference field

The finite ground, packet incidence, nonnegative compensated rates, genuine
product Poisson law and natural-valued coordinates are explicit Mathlib-only
definitions. The statements concern the reference field in main lemma 20.1,
with arbitrary finite packets and heterogeneous intensities where indicated.
-/

namespace PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

local instance referenceDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def incidence (E : Finset (Finset ℕ)) (q : Finset ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ e∈E,if x∈e then q e else 0

abbrev Channel (G : Finset ℕ) (E : Finset (Finset ℕ)) := ↥G ⊕ ↥E

def arrivalRate (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) : Channel G E → ℝ≥0
  | Sum.inl x => ⟨p x.val-incidence E q x.val,hp x.val x.property⟩
  | Sum.inr e => ⟨q e.val,hq e.val e.property⟩

def arrivalMeasure (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) :
    Measure (Channel G E → ℕ) :=
  Measure.pi (fun a ↦ poissonMeasure (arrivalRate G E p q hp hq a))

def field (G : Finset ℕ) (E : Finset (Finset ℕ))
    (ω : Channel G E → ℕ) (x : G) : ℕ :=
  ω (Sum.inl x)+∑ e : E,if x.val∈e.val then ω (Sum.inr e) else 0

def block (G : Finset ℕ) (E : Finset (Finset ℕ)) (A : Finset G) :
    (Channel G E → ℕ) → (A → ℕ) := fun ω x ↦ field G E ω x.val


theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.incidence_eq (E : Finset (Finset ℕ)) (q : Finset ℕ → ℝ) (x : ℕ) :
    incidence E q x=PaperP1.PositionalCompoundPoisson.incidence E q x := by
  unfold incidence PaperP1.PositionalCompoundPoisson.incidence
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hx : x∈e
  · simp only [hx,ite_true]
  · simp only [hx,ite_false]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.source_single_nonneg (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) :
    ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x := by
  simpa only [incidence_eq] using hp

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.arrivalRate_eq (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x)
    (hpS : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) :
    arrivalRate G E p q hp hq=
      PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq := by
  funext a
  apply Subtype.ext
  cases a with
  | inl x =>
    change p x.val-incidence E q x.val=
      p x.val-PaperP1.PositionalCompoundPoisson.incidence E q x.val
    rw [incidence_eq]
  | inr e => rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.arrivalMeasure_eq (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x)
    (hpS : ∀ x∈G,0≤p x-PaperP1.PositionalCompoundPoisson.incidence E q x)
    (hq : ∀ e∈E,0≤q e) :
    arrivalMeasure G E p q hp hq=
      (PaperP1.PositionalPoissonRealization.poissonProduct
        (PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq)).val := by
  unfold arrivalMeasure
  rw [arrivalRate_eq G E p q hp hpS hq]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.field_eq (G : Finset ℕ) (E : Finset (Finset ℕ))
    (ω : Channel G E → ℕ) (x : G) :
    field G E ω x=(∑ a : Channel G E,
      ω a • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val := by
  rw [PaperP1.PositionalPoissonRealization.field_coordinate]
  unfold field
  congr 1
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hx : x.val∈e.val
  · simp only [hx,ite_true]
  · simp only [hx,ite_false]

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.field_function_eq (G : Finset ℕ) (E : Finset (Finset ℕ)) (x : G) :
    (fun ω ↦ field G E ω x)=(fun ω ↦ (∑ a : Channel G E,
      ω a • PaperP1.PositionalPoissonRealization.channelJump G E a) x.val) := by
  funext ω
  exact field_eq G E ω x

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.realField_eq (G : Finset ℕ) (E : Finset (Finset ℕ)) (x : G) :
    (fun ω ↦ (field G E ω x : ℝ))=
      PaperP1.PositionalArrivalCovariance.coordinate G E (fun a ω ↦ ω a) x := by
  funext ω
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) (field_eq G E ω x)

theorem _root_.PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference.block_eq (G : Finset ℕ) (E : Finset (Finset ℕ)) (A : Finset G) :
    block G E A=PaperP1.PositionalBlockIndependence.block G E (fun a ω ↦ ω a) A := by
  funext ω x
  exact field_eq G E ω x.val

theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_reference_exact_marginals (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e) (x : G) :
    ∃ r : ℝ≥0,(r : ℝ)=p x.val ∧
      HasLaw (fun ω ↦ field G E ω x) (poissonMeasure r) (arrivalMeasure G E p q hp hq) ∧
      ∀ j : ℕ,Integrable (fun ω ↦ ((field G E ω x).descFactorial j : ℝ))
        (arrivalMeasure G E p q hp hq) ∧
        (∫ ω,((field G E ω x).descFactorial j : ℝ) ∂arrivalMeasure G E p q hp hq)=p x.val^j := by

  let hpS := source_single_nonneg G E p q hp
  obtain ⟨r,hr,hLaw⟩ := PaperP1.PositionalArrivalMarginals.hasLaw_canonical_coordinate
    G E p q hpS hq x
  have hNative : HasLaw (fun ω ↦ field G E ω x) (poissonMeasure r)
      (arrivalMeasure G E p q hp hq) := by
    rw [arrivalMeasure_eq G E p q hp hpS hq,field_function_eq G E x]
    exact hLaw
  refine ⟨r,hr,hNative,?_⟩
  intro j
  have h := PaperP1.PositionalArrivalMarginals.factorial_moment_of_hasLaw
    (arrivalMeasure G E p q hp hq) (fun ω ↦ field G E ω x) r hNative j
  simpa only [hr] using h

theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_reference_covariance_matrix (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (x y : G) :
    cov[fun ω ↦ (field G E ω x : ℝ),fun ω ↦ (field G E ω y : ℝ);
      arrivalMeasure G E p q hp hq] =
      if x=y then p x.val else if {x.val,y.val}∈E then q {x.val,y.val} else 0 := by

  let hpS := source_single_nonneg G E p q hp
  have h := PaperP1.PositionalArrivalCovariance.covariance_canonical_pairs
    G E p q hpS hq hE x y
  rw [← arrivalMeasure_eq G E p q hp hpS hq,← realField_eq G E x,← realField_eq G E y] at h
  have hd : (fun a b : ℕ ↦ PaperP1.PositionalArrivalCovariance.covarianceDecidable (a=b))=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h

theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_reference_pair_independence (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (x y : G) (hxy : x≠y) :
    IndepFun (fun ω ↦ field G E ω x) (fun ω ↦ field G E ω y)
      (arrivalMeasure G E p q hp hq) ↔ {x.val,y.val}∉E ∨ q {x.val,y.val}=0 := by

  let hpS := source_single_nonneg G E p q hp
  let μS := PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq
  let P : Measure (Channel G E → ℕ) :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).val
  let : IsProbabilityMeasure P :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).property
  have h := PaperP1.PositionalArrivalIndependence.independent_pair_counts_iff
    G E p q hpS hq hE P (fun a ω ↦ ω a)
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval μS)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent μS) x y hxy
  dsimp only [P,μS] at h
  rw [← arrivalMeasure_eq G E p q hp hpS hq,
    ← field_function_eq G E x,← field_function_eq G E y] at h
  have hd : (fun a b : ℕ ↦ PaperP1.PositionalArrivalIndependence.independenceDecidable (a=b))=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h

theorem _root_.PaperP1Registry.Registration.PoissonFields.poisson_reference_block_dependency (G : Finset ℕ) (E : Finset (Finset ℕ))
    (p : ℕ → ℝ) (q : Finset ℕ → ℝ)
    (hp : ∀ x∈G,0≤p x-incidence E q x) (hq : ∀ e∈E,0≤q e)
    (hE : ∀ e∈E,e.card=2) (A B : Finset G) (hAB : Disjoint A B) :
    IndepFun (block G E A) (block G E B) (arrivalMeasure G E p q hp hq) ↔
      ∀ x∈A,∀ y∈B,¬({x.val,y.val}∈E ∧ 0<q {x.val,y.val}) := by

  let hpS := source_single_nonneg G E p q hp
  let μS := PaperP1.PositionalPoissonRealization.channelRate G E p q hpS hq
  let P : Measure (Channel G E → ℕ) :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).val
  let : IsProbabilityMeasure P :=
    (PaperP1.PositionalPoissonRealization.poissonProduct μS).property
  have h := PaperP1.PositionalBlockIndependence.independent_pair_blocks_iff_no_positive_crossing
    G E p q hpS hq hE P (fun a ω ↦ ω a)
    (PaperP1.PositionalPoissonRealization.poissonProduct_hasLaw_eval μS)
    (PaperP1.PositionalPoissonRealization.poissonProduct_independent μS) A B hAB
  dsimp only [P,μS] at h
  rw [← arrivalMeasure_eq G E p q hp hpS hq,← block_eq G E A,← block_eq G E B] at h
  have hd : (fun a b : ℕ ↦ PaperP1.PositionalBlockIndependence.blockDecidable (a=b))=instDecidableEqNat :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h


end PaperP1Registry.RegistrationModels.PoissonFields.PoissonReference

end ComponentPoissonReference
