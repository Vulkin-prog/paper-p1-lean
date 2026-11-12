module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import PaperP1.Asymptotics.SharpThirdActivity
public import PaperP1.Asymptotics.FourthCumulantIdentities
public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Asymptotics.FixedArityHomogeneousMass

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

/-! # P1 V2: Third and fourth cumulants and optimal quadratic error

Selected statements cover main article results 3.3–3.4,6.1–6.2. Literal definitions specify
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

namespace PaperP1Registry.V2.CumulantsOptimality
open Finset MeasureTheory
open scoped BigOperators
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

/-- Actual real-valued indicator of a start, of either sign. -/
def indicator (x L : ℕ) (ω : Sample) : ℝ := if startIndicator x L ω then 1 else 0

/-- Actual heterogeneous one-window probability. -/
def marginal (x L : ℕ) : ℝ := ∫ ω, indicator x L ω ∂primeSignMeasure

/-- Actual joint start mass, including incompatible families. -/
def jointMoment (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, indicator x L ω ∂primeSignMeasure

/-- Actual centered joint coefficient, using every window's own mean. -/
def centeredCoefficient (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicator x L ω-marginal x L) ∂primeSignMeasure

/-- Actual falling-factorial moment of the complete count. -/
def factorialMoment (N L r : ℕ) : ℝ :=
  ∫ ω, ((runCount N L ω).descFactorial r : ℝ) ∂primeSignMeasure

/-- Third factorial cumulant of the literal count law. -/
def thirdCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 3-3*factorialMoment N L 2*factorialMoment N L 1+2*(factorialMoment N L 1)^3

/-- Fourth factorial cumulant of the literal count law. -/
def fourthCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 4-4*factorialMoment N L 3*factorialMoment N L 1-
    3*(factorialMoment N L 2)^2+12*factorialMoment N L 2*(factorialMoment N L 1)^2-
    6*(factorialMoment N L 1)^4

/-- The literal moving residue-dependent scale of the second cumulant. -/
def principalSecondScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(18*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*L*(N : ℝ)^(-2/3 : ℝ)

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

/-- All falling-factorial observables are genuinely integrable, and their
subset expansion uses the actual joint probabilities of the original starts. -/
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

/-- Exact third-cumulant identity, including every heterogeneous marginal
and repeated-index correction, at all finite scales. -/
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

/-- Exact fourth-cumulant identity with the complete pair-square, triple,
heterogeneous pair and diagonal terms. No common marginal is substituted. -/
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

/-- Full critical-band equivalent of the actual second factorial cumulant,
with the exact moving residue coefficient and nominal mean. -/
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

/-- The optimal positive 41/30 power for the actual third factorial cumulant.
The positive lower constant depends only on C, before the upper margin. -/
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


/-- Vertex labels include the predecessor and every letter of the word. -/
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

/-- Effective square classes: local relations are quotiented out once. -/
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

/-- Connectedness is the actual finest direct partition, not pairwise overlap. -/
def Connected (L : ℕ) (I : Finset ℕ) : Prop := canonicalPartition (fun i : I ↦ space i.val L)=⊤

def connectedFamilies (N L r : ℕ) : Finset (Finset ℕ) :=
  ((Ico N (2*N)).powersetCard r).filter (Connected L)

def relativeNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.ker (addition (fun i : I ↦ space i.val L)))

def compatibleNullity (L : ℕ) (I : Finset ℕ) : ℕ :=
  I.powerset.sup fun A ↦ if 0 < jointMoment L A then relativeNullity L A else 0

/-- Zero-target homogeneous mass, equivalently the reciprocal effective rank. -/
def totalSpace (L : ℕ) (I : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  ⨆ i : I, space i.val L

def homogeneousMass (L : ℕ) (I : Finset ℕ) : ℝ :=
  (2 ^ Module.finrank F₂ (totalSpace L I) : ℝ)⁻¹

def rankWeight (L : ℕ) (I : Finset ℕ) : ℝ :=
  (∏ x ∈ I, marginal x L)*(2 ^ relativeNullity L I : ℝ)

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

/-- Actual compatible connected quartic mass, with its nonnegative sign. -/
def quarticPositive (N L : ℕ) : ℝ :=
  ∑ I ∈ (connectedFamilies N L 4).filter (fun I ↦ 0 < jointMoment L I), centeredCoefficient L I

def quarticSigned (N L : ℕ) : ℝ :=
  ∑ I ∈ connectedFamilies N L 4, centeredCoefficient L I

def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)
def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k
def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)
def quadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|

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

/-- V2 Corollary3.4: the complete absolute triple activity is below4/3. -/
theorem absolute_triple_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑ I ∈ (Ico N (2*N)).powersetCard 3, |centeredCoefficient L I|) ≤
        (N : ℝ)^(-41/30+ε) := by
  obtain ⟨N₀,_hN₀,h⟩ := PaperP1.SharpThirdActivity.article_14_6 C ε hε
  refine ⟨max 4 N₀,by omega,?_⟩
  intro N hN L hband
  simpa only [centeredCoefficient_eq,PaperP1.CompatibleActivitySplit.absolute,
    PaperP1.Model.dyadicBlock] using h N (by omega) L hband (PaperP1.Model.dyadicBlock N) Subset.rfl

/-- V2 Lemma6.1: the quartic identity retains compatible positive activity,
and distinguishes5/3 from3/2 errors. No pair square is silently dropped. -/
theorem quartic_non_cancellation (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      0 ≤ quarticPositive N L ∧
      |fourthCumulant N L-24*quarticSigned N L| ≤ (N : ℝ)^(-5/3+ε) ∧
      |quarticSigned N L-quarticPositive N L| ≤ (N : ℝ)^(-3/2+ε) ∧
      |fourthCumulant N L+3*(secondCumulant N L)^2-
        (3*(secondCumulant N L)^2+24*quarticPositive N L)| ≤ (N : ℝ)^(-3/2+ε) := by
  simpa only [quarticPositive,quarticSigned,connectedFamilies_eq,jointMoment_eq,
    centeredCoefficient_eq,fourth_eq,second_eq,PaperP1.CompatibleActivitySplit.positive,
    PaperP1.CompatibleActivitySplit.signed] using PaperP1.FourthCumulantIdentities.article_16_1 C ε hε

/-- V2 Theorem6.2: matching upper/lower powers for the exact quadratic reference. -/
theorem quadratic_optimality (C ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      a*(N : ℝ)^(-4/3-ε) ≤ quadraticError N L ∧
      quadraticError N L ≤ (N : ℝ)^(-4/3+ε) := by
  simpa only [error_eq] using PaperP1.OptimalQuadratic.article_16_2 C ε hε

end PaperP1Registry.V2.CumulantsOptimality
