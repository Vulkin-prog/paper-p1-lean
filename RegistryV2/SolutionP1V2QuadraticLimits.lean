module

public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Asymptotics.OptimalZeroProbability
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

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

/-! # P1 V2: Exact quadratic approximation, Poisson scales and weighted consequences

Selected statements cover main article results 1.1–1.2,7.2–7.4. Literal definitions specify
the independent prime-sign model, exact observables, reference laws and error
norms. Parameters and thresholds retain their printed order. The companion
supplies substantive proofs through the parent development in this repository.
The corresponding six-dossier coverage map records each complete clause bundle.
Only the selected Challenge theorem proofs are deliberate statement holes;
the Solution and its bridge proofs contain no placeholders.
Selected model foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.V2.QuadraticLimits

open Finset MeasureTheory

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

def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)

def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k

def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)

def actualPoissonTV (N L : ℕ) : ℝ :=
  (∑' k : ℕ, |sourceMass N L k-poissonMass (actualMean N L) k|)/2

def nominalPoissonTV (N L : ℕ) : ℝ :=
  (∑' k : ℕ, |sourceMass N L k-poissonMass (nominalMean N L) k|)/2

def secondDifferenceMass (μ : ℝ) (k : ℕ) : ℝ :=
  shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k

def secondNorm (μ : ℝ) : ℝ := ∑' k : ℕ, |secondDifferenceMass μ k|

def phaseScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(72*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*secondNorm (nominalMean N L)*L*(N : ℝ)^(-2/3 : ℝ)

def nominalQuadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (nominalMean N L) (secondCumulant N L) k|

def quadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|

def factorialMoment (N L r : ℕ) : ℝ :=
  ∫ ω, ((runCount N L ω).descFactorial r : ℝ) ∂primeSignMeasure

def referenceMoment (μ α : ℝ) (r : ℕ) : ℝ :=
  μ ^ r + (r.choose 2 : ℝ) * μ ^ (r - 2) * α

def weightedError (N L m : ℕ) : ℝ :=
  ∑' k : ℕ, (1 + (k : ℝ)) ^ m *
    |sourceMass N L k - quadraticMass (actualMean N L) (secondCumulant N L) k|

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

def marginal (x L : ℕ) : ℝ := ∫ ω, (if startIndicator x L ω then (1 : ℝ) else 0) ∂primeSignMeasure

def integerBias (N L : ℕ) : ℤ :=
  ∑ x ∈ Ico N (2*N), (((if 0<marginal x L then 2^(L-Module.finrank F₂ (space x L)) else 0 : ℕ) : ℤ)-1)

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

theorem mean_bias_quantized (N L : ℕ) (hN : 2 ≤ N) (hL : 0 < L) :
    ∃ b : ℤ, actualMean N L-nominalMean N L = (2^L : ℝ)⁻¹*(b : ℝ) ∧
      (actualMean N L=nominalMean N L ∨
        (2^L : ℝ)⁻¹ ≤ |actualMean N L-nominalMean N L|) :=
by
  obtain ⟨hi,hd⟩ := (PaperP1.OptimalNominalQuadratic.article_17_3 0 1 (by norm_num)).1 N L hN hL
  refine ⟨PaperP1.MeanBiasQuantization.bias (PaperP1.Model.dyadicBlock N) L,?_,?_⟩
  · simpa only [actualMean_eq,nominalMean_eq] using hi
  · simpa only [actualMean_eq,nominalMean_eq,PaperP1.OptimalNominalQuadratic.meanGap] using hd

theorem nominal_quadratic_comparison (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      nominalQuadraticError N L ≤ (N : ℝ)^(-1+ε) ∧
      (actualMean N L≠nominalMean N L →
        c*|actualMean N L-nominalMean N L| ≤ nominalQuadraticError N L ∧
        nominalQuadraticError N L ≤ (6+c)*|actualMean N L-nominalMean N L|) :=
by
  refine ⟨PaperP1.OptimalNominalQuadratic.lowerConstant C,
    PaperP1.OptimalNominalQuadratic.lowerConstant_pos C,?_⟩
  intro ε hε
  obtain ⟨N₀,h₀,h⟩ := PaperP1.OptimalNominalQuadratic.uniform_comparison C ε hε
  obtain ⟨NG,hGeometry⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max N₀ NG,by omega,?_⟩
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

theorem error_eq (N L : ℕ) : quadraticError N L = PaperP1.OptimalQuadratic.error N L := by
  simpa only [quadraticError,sourceMass_eq,quadraticMass_eq,actualMean_eq,cumulant_eq,
    PaperP1.OptimalQuadratic.error,PaperP1.OptimalQuadratic.reference] using
    (PaperP1.FourthCharlierLawDistance.distance_eq_sequence
      (PaperP1.RetainedModifiedLaw.originalLaw (PaperP1.Model.dyadicBlock N) L)
      (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L)
      (by simpa only [actualMean_eq] using mean_nonneg N L)).symm

theorem reference_series (N L : ℕ) :
    HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 ∧
    Summable (fun k : ℕ ↦ |sourceMass N L k-
      quadraticMass (actualMean N L) (secondCumulant N L) k|) :=
by
  have hSum : HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 := by
    simpa only [quadraticMass_fun_eq] using
      PaperP1.PoissonSequence.hasSum_quadraticMass (actualMean N L) (secondCumulant N L) (mean_nonneg N L)
  exact ⟨hSum,((source_probability N L).2.2.2.summable.sub hSum.summable).abs⟩

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

theorem factorialMoment_eq (N L r : ℕ) :
    factorialMoment N L r=PaperP1.FactorialCountMoments.factorialCountMoment
      (PaperP1.Model.dyadicBlock N) L r := by rfl

theorem polynomial_weights (C ε : ℝ) (hε : 0 < ε) :
    (∀ m : ℕ, ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      Summable (fun k : ℕ ↦ (1 + (k : ℝ)) ^ m *
        |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|) ∧
      weightedError N L m ≤ (N : ℝ)^(-4/3+ε)) ∧
    (∀ r : ℕ, ∃ N₁ : ℕ, 2 ≤ N₁ ∧ ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      |factorialMoment N L r-referenceMoment (actualMean N L) (secondCumulant N L) r| ≤
        (N : ℝ)^(-4/3+ε)) ∧
    ∀ N L : ℕ, factorialMoment N L 0=1 ∧ factorialMoment N L 1=actualMean N L ∧
      factorialMoment N L 2=(actualMean N L)^2+secondCumulant N L := by
  simpa only [weightedError,PaperP1.PolynomialWeightedQuadratic.weightedError,
    sourceMass_eq,quadraticMass_eq,actualMean_eq,cumulant_eq,factorialMoment_eq,
    PaperP1.ActualQuadraticSubpowerMoments.original,PaperP1.ActualQuadraticSubpowerMoments.quadratic,
    referenceMoment,PaperP1.QuadraticFactorialMomentTransfer.referenceMoment] using
    PaperP1.PolynomialWeightedQuadratic.article_17_1 C ε hε

theorem no_retained_start (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      |sourceMass N L 0-Real.exp (-actualMean N L)*(1+secondCumulant N L/2)| ≤
        (N : ℝ)^(-4/3+ε) := by
  simpa only [sourceMass_eq,actualMean_eq,cumulant_eq,
    PaperP1.ActualQuadraticSubpowerMoments.original] using
    PaperP1.OptimalZeroProbability.article_17_2 C ε hε

theorem integerBias_eq (N L : ℕ) : integerBias N L=
    PaperP1.MeanBiasQuantization.bias (PaperP1.Model.dyadicBlock N) L := by
  have hs (x : ℕ) : space x L=PaperP1.Arithmetic.squareClassSpace x L := by rfl
  have hd (x : ℕ) : Module.finrank F₂ (space x L)=Module.finrank F₂ (PaperP1.Arithmetic.squareClassSpace x L) := by rw [hs]
  have hm (x : ℕ) : marginal x L=PaperP1.Model.InfiniteStarts.infiniteMarginal x L := by rfl
  simp only [integerBias,PaperP1.MeanBiasQuantization.bias,PaperP1.MeanBiasQuantization.coefficient,
    PaperP1.MeanBiasQuantization.localMultiplicity,PaperP1.MeanBiasQuantization.deficiency,hd,hm,
    PaperP1.Model.dyadicBlock]

theorem literal_mean_bias (N L : ℕ) (hN : 2≤N) (hL : 0<L) :
    actualMean N L-nominalMean N L=(2^L : ℝ)⁻¹*(integerBias N L : ℝ) ∧
    ∀ C : ℝ, |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ((2 : ℝ)^C)⁻¹/N ≤ (2^L : ℝ)⁻¹ ∧ (2^L : ℝ)⁻¹ ≤ (2 : ℝ)^C/N := by
  constructor
  · simpa only [actualMean_eq,nominalMean,integerBias_eq] using
      PaperP1.MeanBiasQuantization.main_17_3_integer_identity hN hL
  · intro C hband
    refine ⟨PaperP1.CriticalChannelPowers.nominal_lower hN hband,?_⟩
    have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
    apply (le_div_iff₀ hn).2
    have h := (PaperP1.FiniteChannelHierarchyBounds.nominal_bounds hN hband).2
    change (N : ℝ)*(2^L : ℝ)⁻¹ ≤ (2 : ℝ)^C at h
    simpa only [mul_comm] using h

end PaperP1Registry.V2.QuadraticLimits
