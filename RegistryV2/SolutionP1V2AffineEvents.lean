module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.Ring.Basic
public import PaperP1.Algebra.StoppedExpansion
public import PaperP1.Asymptotics.V2HomogeneousEnvelope
public import PaperP1.Model.SquareClassFourier
public import PaperP1.Model.UnrestrictedRunComponents
public import PaperP1.Probability.CenteredMeasureExpansion
public import PaperP1.Probability.StoppedMeasureLaw

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

/-! # P1 V2: Exact affine events and homogeneous envelopes

Selected statements cover main article results 2.1–2.5. Literal definitions specify
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
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace PaperP1Registry.V2.AffineEvents
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


open Finset MeasureTheory
open scoped Classical BigOperators

variable {ι Ω : Type*}

/-- Prefix with the greatest element removed, also defined on the empty set. -/
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

/-- Ordinary unweighted singleton l1 norm. -/
def expansion_l1Norm (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ |r|

def expansion_totalMass (ν : expansion_SignedLaw) : ℝ := ν.coeff.sum fun _ r ↦ r

def expansion_indicator (b : Bool) : ℝ := if b then 1 else 0

def expansion_count (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) : ℕ :=
  ∑ x ∈ G, (J x ω).toNat

/-- All expansion_count probabilities, represented on their literal finite support. -/
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

/-- A signed reference of mass one, whose coefficients need not be positive. -/
def expansion_retainedReference [MeasurableSpace Ω] (G : Finset ι) (D : Finset ι → Prop)
    (μ : Measure Ω) (J : ι → Ω → Bool) : expansion_SignedLaw :=
  ∑ I ∈ expansion_retained G D, expansion_scalar (expansion_jointMoment μ J I)*expansion_difference^I.card


/-- Finite reconstruction uses the literal coefficient sequence. -/
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

/-- Exact first-excluded-prefix identity, already over a commutative semiring. -/
theorem expansion_polynomial_expansion {R : Type*} [LinearOrder ι] [CommSemiring R]
    (G : Finset ι) (D : Finset ι → Prop) (u : ι → R) (t : R)
    (hD : expansion_Hereditary D) (h0 : D ∅) :
    (∏ x ∈ G, (1+t*u x))=
      (∑ I ∈ expansion_retained G D, t^I.card*∏ x ∈ I, u x)+
      ∑ I ∈ expansion_boundary G D, (t^I.card*∏ x ∈ I, u x)*
        ∏ y ∈ expansion_suffix G I, (1+t*u y) :=
by
  exact PaperP1.Algebra.stopped_expansion G D u t hD h0

/-- The exact actual law, with heterogeneous marginals and arbitrary dependence.
Its coefficients are the original expansion_count probabilities and it is normalized. -/
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

/-- Each positive kernel has the actual prefix/expansion_suffix joint expectation as
its coefficients and exactly the prefix activation probability as mass/norm.
The expansion_suffix is allowed to depend on the entire prefix. -/
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

/-- Ordinary l1 error depends only on the ordered expansion_boundary activity mass;
there is no factor charging the number of dependent expansion_suffix indicators. -/
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


instance finiteSpace (x L : ℕ) : Fintype (space x L) := by
  classical
  let : Fintype (LinearMap.ker (vertexSum L)) := Fintype.ofFinite _
  exact Fintype.ofSurjective (evenParity x L).rangeRestrict (by
    rintro ⟨c,⟨w,hw⟩⟩
    exact ⟨w,Subtype.ext hw⟩)

/-- An actual finite prime cylinder, with the inclusive cutoff of the paper. -/
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

/-- V2 Lemma2.2 on any finite indexed family. Affine signs, nonzero effective
projections, actual heterogeneous marginals and the minus-one bound are explicit. -/
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

/-- V2 Lemma2.3: one exact envelope for all three original weights, including
inconsistent prescriptions and zero original marginals. -/
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

/-- The same threshold precedes every family; the growing-order factor remains. -/
theorem nominal_envelope (C : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ Ico N (2*N) →
        homogeneousMass L I ≤ (2 : ℝ)^I.card*((2 ^ L : ℝ)⁻¹)^I.card*
          (2 ^ relativeNullity L I : ℝ) := by
  simpa only [homogeneousMass_eq,relativeNullity_eq,PaperP1.PrimitiveNominalMass.weight,
    PaperP1.Model.InfiniteStarts.runRelativeNullity,PaperP1.Model.dyadicBlock,mul_assoc] using
    PaperP1.V2HomogeneousEnvelope.uniform_nominal_comparison C

/-- V2 Lemma2.4: maximum nullity over positive compatible subfamilies, not raw rank loss. -/
theorem compatible_nullity (L : ℕ) (hL : 0 < L) (I : Finset ℕ)
    (hp : ∀ x ∈ I, 0 < marginal x L) :
    |centeredCoefficient L I| ≤ (2 : ℝ)^I.card*(∏ x ∈ I, marginal x L)*
      (2 ^ compatibleNullity L I : ℝ) ∧
    compatibleNullity L I ≤ relativeNullity L I ∧
    (0 < jointMoment L I → compatibleNullity L I=relativeNullity L I) := by
  exact ⟨PaperP1.Model.InfiniteStarts.infinite_centered_compatible_nullity_bound L I hL hp,
    PaperP1.Model.InfiniteStarts.runCompatibleNullity_le_relative L I,
    PaperP1.Model.InfiniteStarts.runCompatibleNullity_eq_of_positive_joint L I⟩

/-- V2 Lemma2.5: unique finest partition preserving every zero-sum effective relation. -/
theorem unique_direct_partition {U ι : Type*} [AddCommGroup U] [Module F₂ U]
    [Fintype ι] [DecidableEq ι] (S : ι → Submodule F₂ U) :
    ∃! P : Finpartition (univ : Finset ι), RespectsRelations S P ∧
      ∀ Q : Finpartition (univ : Finset ι), RespectsRelations S Q → P ≤ Q := by
  exact PaperP1.Affine.existsUnique_finest_relationPartition S

def partImage {I : Finset ℕ} (C : Finset I) : Finset ℕ := C.image fun i ↦ i.val

/-- All probability, centered and nullity factorizations use the same canonical
partition, including zero marginals; no independence assumption is supplied. -/
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

/-- The unit, singleton cancellation and deterministic complementary probabilities
complete every clause of V2 Proposition2.1. -/
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

end PaperP1Registry.V2.AffineEvents
