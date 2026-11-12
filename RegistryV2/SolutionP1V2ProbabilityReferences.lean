module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic
public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Asymptotics.OptimalHermite
public import PaperP1.Asymptotics.FixedHeightHierarchy
public import PaperP1.Asymptotics.TwoChannelReference

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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import PaperP1.Asymptotics.OptimalThirdCumulant
public import PaperP1.Asymptotics.ActualPairPhase
public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Model.RetainedMomentTransfer

/-! # P1 V2: Probability domain and actual single/double-jump Hermite laws

Selected statements cover main article results 7.1,8.4. Literal definitions specify
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

namespace PaperP1Registry.V2.ProbabilityReferences

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

end PaperP1Registry.V2.ProbabilityReferences
