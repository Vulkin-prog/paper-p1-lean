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
public import PaperP1.Asymptotics.ExactPoissonScale
public import PaperP1.Asymptotics.OptimalNominalQuadratic
public import PaperP1.Model.RetainedMomentTransfer

/-! # Exact Poisson scales and quantized mean bias for multiplicative runs

The independent prime-sign model and actual count masses are explicit. The
two Poisson means have a common moving residue-dependent equivalent; changing
the mean of the quadratic reference has a separate quantized cost. The latter
comparison applies on biased scales and asserts no infinitude of such scales.
The model foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the five selected Challenge theorem holes are deliberate placeholders.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.PoissonScales
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

theorem nominalMean_eq (N L : ℕ) : nominalMean N L = PaperP1.FiniteChannelHierarchy.nominalMean N L := by rfl

theorem nominal_nonneg (N L : ℕ) : 0 ≤ nominalMean N L := by
  unfold nominalMean
  positivity

theorem poissonLaw_realMass (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) :
    PaperP1.AtomicProbability.realMass (PaperP1.QuadraticPoisson.poissonLaw μ hμ) k = poissonMass μ k := by
  exact ProbabilityTheory.poissonMeasure_real_singleton ⟨μ,hμ⟩ k

theorem actualTV_eq (N L : ℕ) : actualPoissonTV N L = PaperP1.ExactPoissonScale.actualTV N L := by
  unfold actualPoissonTV PaperP1.ExactPoissonScale.actualTV PaperP1.AtomicProbability.totalVariation
  congr 1
  apply tsum_congr
  intro k
  change |sourceMass N L k-poissonMass (actualMean N L) k| =
    |PaperP1.AtomicProbability.realMass (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k-
      PaperP1.AtomicProbability.realMass (PaperP1.ExactPoissonScale.actualPoisson N L) k|
  rw [sourceMass_eq,PaperP1.ExactPoissonScale.actualPoisson,poissonLaw_realMass,actualMean_eq]

theorem nominalTV_eq (N L : ℕ) : nominalPoissonTV N L = PaperP1.ExactPoissonScale.nominalTV N L := by
  unfold nominalPoissonTV PaperP1.ExactPoissonScale.nominalTV PaperP1.AtomicProbability.totalVariation
  congr 1
  apply tsum_congr
  intro k
  change |sourceMass N L k-poissonMass (nominalMean N L) k| =
    |PaperP1.AtomicProbability.realMass (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L) k-
      PaperP1.AtomicProbability.realMass (PaperP1.ExactPoissonScale.nominalPoisson N L) k|
  rw [sourceMass_eq,PaperP1.ExactPoissonScale.nominalPoisson,poissonLaw_realMass,nominalMean_eq]

theorem difference_two (a : ℕ → ℝ) :
    PaperP1.FiniteShiftAction.difference 2 a = PaperP1.PoissonSequence.secondDifference a := by
  have hShift : PaperP1.PoissonSequence.shift (PaperP1.PoissonSequence.shift a-a) =
      PaperP1.PoissonSequence.shift (PaperP1.PoissonSequence.shift a)-PaperP1.PoissonSequence.shift a :=
    map_sub PaperP1.FiniteShiftAction.shiftLinear _ _
  simp only [PaperP1.FiniteShiftAction.difference_succ,PaperP1.FiniteShiftAction.difference_zero]
  rw [hShift]
  funext k
  simp only [PaperP1.PoissonSequence.secondDifference,Pi.sub_apply]
  ring

theorem secondNorm_eq (μ : ℝ) (hμ : 0 ≤ μ) : secondNorm μ = PaperP1.PoissonDifferenceSigned.norm μ 2 := by
  rw [PaperP1.PoissonDifferenceSigned.norm_eq_l1 μ hμ 2]
  unfold secondNorm PaperP1.IteratedPoissonDifferences.l1
  rw [difference_two]
  rfl

theorem phaseScale_eq (N L : ℕ) : phaseScale N L = PaperP1.ExactPoissonScale.phaseScale N L := by
  unfold phaseScale
  rw [secondNorm_eq _ (nominal_nonneg N L),nominalMean_eq]
  exact (PaperP1.ExactPoissonScale.phaseScale_formula N L).symm

theorem nominal_error_eq (N L : ℕ) :
    nominalQuadraticError N L = PaperP1.OptimalNominalQuadratic.nominalError N L := by
  simpa only [nominalQuadraticError,sourceMass_eq,quadraticMass_eq,nominalMean_eq,cumulant_eq,
    PaperP1.OptimalNominalQuadratic.nominalError] using
    (PaperP1.FourthCharlierLawDistance.distance_eq_sequence
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)
      (PaperP1.FiniteChannelHierarchy.nominalMean N L)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L)
      (by simpa only [nominalMean_eq] using nominal_nonneg N L)).symm

/-- Measurability, all finite moments and normalization of the literal source. -/
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

/-- Complete first-order Poisson comparisons for both means, retaining the
actual second factorial cumulant and their distinct error powers. -/
theorem poisson_expansion (C ε : ℝ) (hε : 0 < ε) :
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
theorem moving_residue_equivalent (C : ℝ) :
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
theorem mean_bias_quantized (N L : ℕ) (hN : 2 ≤ N) (hL : 0 < L) :
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
theorem nominal_quadratic_comparison (C ε : ℝ) (hε : 0 < ε) :
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

end PaperP1Registry.PoissonScales
