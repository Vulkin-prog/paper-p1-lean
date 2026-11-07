module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.NormNum
public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Model.RetainedMomentTransfer

/-! # Optimal quadratic approximation of actual multiplicative-run counts

The random prime signs, literal run starts, actual mean and second factorial
cumulant, Poisson singleton masses and full l1 error are all defined below
using Mathlib. The finite and infinite model foundations are adapted through
P1 from Paper C, exact commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Apache-2.0; source identities and adaptations are in docs/PAPER_C_REUSE.md.
The four Challenge statement holes are deliberate selections, not proofs.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.QuadraticApproximation
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

theorem runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω = PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by
  rfl

theorem runCount_fun_eq (N L : ℕ) : runCount N L =
    PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L :=
  funext (runCount_eq N L)

theorem moment_eq (N L j : ℕ) :
    moment N L j = PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L j := by
  simp only [moment,runCount_eq,PaperP1.CountObservables.countMoment,
    primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure]

theorem actualMean_eq (N L : ℕ) :
    actualMean N L = PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1 :=
  moment_eq N L 1

theorem cumulant_eq (N L : ℕ) :
    secondCumulant N L = PaperP1.RegularCumulantTransfer.secondFactorialCumulant
      (PaperP1.Model.dyadicBlock N) L := by
  simp only [secondCumulant,actualMean_eq,moment_eq,
    PaperP1.RegularCumulantTransfer.secondFactorialCumulant]

theorem sourceMass_eq (N L k : ℕ) :
    sourceMass N L k = PaperP1.AtomicProbability.realMass
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k := by
  simpa only [sourceMass,runCount_eq,primeSignMeasure,coordinateMeasure,
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure,
    PaperP1.Model.InfiniteRademacher.coordinateMeasure] using
    (PaperP1.RetainedModifiedLaw.realMass_originalLaw (PaperP1.Model.dyadicBlock N) L k).symm

theorem sourceMass_fun_eq (N L : ℕ) : sourceMass N L = PaperP1.AtomicProbability.realMass
    (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) :=
  funext (sourceMass_eq N L)

theorem mean_nonneg (N L : ℕ) : 0 ≤ actualMean N L := by
  unfold actualMean moment
  exact integral_nonneg fun ω ↦ pow_nonneg (Nat.cast_nonneg (runCount N L ω)) 1

theorem quadraticMass_eq (μ α : ℝ) (k : ℕ) :
    quadraticMass μ α k = PaperP1.PoissonSequence.quadraticMass μ α k := by rfl

theorem quadraticMass_fun_eq (μ α : ℝ) : quadraticMass μ α =
    PaperP1.PoissonSequence.quadraticMass μ α := funext (quadraticMass_eq μ α)

theorem error_eq (N L : ℕ) : quadraticError N L = PaperP1.OptimalQuadratic.error N L := by
  simpa only [quadraticError,sourceMass_eq,quadraticMass_eq,actualMean_eq,cumulant_eq,
    PaperP1.OptimalQuadratic.error,PaperP1.OptimalQuadratic.reference] using
    (PaperP1.FourthCharlierLawDistance.distance_eq_sequence
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)
      (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L)
      (by simpa only [actualMean_eq] using mean_nonneg N L)).symm

/-- Measurability, all finite moments, and normalization of the literal source. -/
theorem source_probability (N L : ℕ) :
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
theorem reference_series (N L : ℕ) :
    HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 ∧
    Summable (fun k : ℕ ↦ |sourceMass N L k-
      quadraticMass (actualMean N L) (secondCumulant N L) k|) :=
by
  have hSum : HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 := by
    simpa only [quadraticMass_fun_eq] using
      PaperP1.PoissonSequence.hasSum_quadraticMass (actualMean N L) (secondCumulant N L) (mean_nonneg N L)
  exact ⟨hSum,((source_probability N L).2.2.2.summable.sub hSum.summable).abs⟩

/-- Complete article theorem 1.1: optimal upper and lower powers, exact mean
and second factorial cumulant, quantified nominal-mean bias, and a genuine
probability reference. A single threshold precedes every critical word length. -/
theorem optimal_quadratic (C ε : ℝ) (hε : 0 < ε) :
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
  have hSum := (reference_series N L).1
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
theorem probability_criterion (μ α : ℝ) (hμ : 0 < μ) :
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

end PaperP1Registry.QuadraticApproximation
