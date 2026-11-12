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
public import PaperP1.Asymptotics.FiniteCompleteLawTransfer
public import PaperP1.Asymptotics.FixedArityHomogeneousMass
public import PaperP1.Asymptotics.OptimalQuadratic
public import PaperP1.Asymptotics.OptimalTripleReconstruction
public import PaperP1.Asymptotics.RunConversion
public import PaperP1.Probability.StoppedMeasureLaw
public import PaperP1.Probability.UniversalHeterogeneousConversion

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

/-! # P1 V2: Stopping, heterogeneous conversion and complete-law reconstruction

Selected statements cover main article results 4.1–4.2,5.1–5.3. Literal definitions specify
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

namespace PaperP1Registry.V2.StoppingReconstruction

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

def poissonMass (μ : ℝ) (k : ℕ) : ℝ := Real.exp (-μ)*μ^k/(k.factorial : ℝ)

def shift (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => a k

def quadraticMass (μ α : ℝ) (k : ℕ) : ℝ := poissonMass μ k+
  (α/2)*(shift (shift (poissonMass μ)) k-2*shift (poissonMass μ) k+poissonMass μ k)

def quadraticError (N L : ℕ) : ℝ :=
  ∑' k : ℕ, |sourceMass N L k-quadraticMass (actualMean N L) (secondCumulant N L) k|

def finiteReference {κ : Type*} [DecidableEq κ] (G : Finset κ) (E : Finset (Finset κ))
    (p : κ → ℝ) (c : Finset κ → ℝ) : expansion_SignedLaw :=
  (∏ i ∈ G, expansion_bernoulli (p i))+
    ∑ e ∈ E, expansion_scalar (c e)*expansion_difference^2*
      ∏ i ∈ G \ e, expansion_bernoulli (p i)

def pairReference (N L : ℕ) : expansion_SignedLaw :=
  finiteReference (Ico N (2*N)) ((Ico N (2*N)).powersetCard 2)
    (fun x ↦ marginal x L) (centeredCoefficient L)

def fixedFamilies (N L r : ℕ) : Finset (Finset ℕ) :=
  (connectedFamilies N L r).filter fun I ↦ compatibleNullity L I ≤ 2*L

def FixedActivity (C β : ℝ) : Prop :=
  ∀ r : ℕ, 3 ≤ r → r ≤ 256 → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑ I ∈ fixedFamilies N L r, |centeredCoefficient L I|) ≤ A*(N : ℝ)^(-β+ε)

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

theorem finiteReference_eq {κ : Type*} [DecidableEq κ]
    (G : Finset κ) (E : Finset (Finset κ)) (p : κ → ℝ) (c : Finset κ → ℝ) :
    finiteReference G E p c=PaperP1.HeterogeneousPoissonCharlierConversion.finiteReference G E p c := by rfl

theorem pairReference_eq (N L : ℕ) : pairReference N L=
    PaperP1.HeterogeneousRunConversion.reference (PaperP1.Model.dyadicBlock N) L := by rfl

theorem fixedFamilies_eq (N L r : ℕ) :
    fixedFamilies N L r=PaperP1.FiniteConnectedActivity254.families N L r := by rfl

theorem fixedActivity_eq (C β : ℝ) : FixedActivity C β=PaperP1.FiniteConnectedActivity254.Hypothesis C β := by rfl

theorem prefix_suffix {κ : Type*} [LinearOrder κ] (I G : Finset κ) (hne : I.Nonempty) :
    expansion_properPrefix I=I.erase (I.max' hne) ∧
    expansion_suffix G I=G.filter (fun y ↦ ∀ x ∈ I, x<y) := by
  exact ⟨PaperP1.Algebra.properPrefix_eq_erase_max I hne,rfl⟩

theorem finite_conversion {κ : Type*} [DecidableEq κ]
    (G : Finset κ) (E : Finset (Finset κ)) (p : κ → ℝ) (c : Finset κ → ℝ)
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card=2) (hp : ∀ i ∈ G, 0 ≤ p i ∧ p i ≤ 1)
    (P : ℝ) (hP : 0 ≤ P) (hcap : ∀ i ∈ G, p i ≤ P) :
    (∑' k : ℕ, |(finiteReference G E p c).coeff k-
      quadraticMass (∑ i ∈ G, p i) (2*(∑ e ∈ E, c e)-∑ i ∈ G, (p i)^2) k|) ≤
      16*Real.exp 2*((∑ i ∈ G, (p i)^3)+(∑ i ∈ G, (p i)^2)^2+
        (∑ e ∈ E, |c e|)*((∑ i ∈ G, (p i)^2)+P)) := by
  have hμ := PaperP1.HeterogeneousBernoulli.mean_nonneg G p (fun i hi ↦ (hp i hi).1)
  have href (k : ℕ) : PaperP1.QuadraticPoisson.reference
      (PaperP1.HeterogeneousBernoulli.mean G p)
      (2*PaperP1.HeterogeneousPoissonCharlierConversion.covarianceSum E c-
        PaperP1.HeterogeneousBernoulli.powerSum G p 2) {k}=
      PaperP1.PoissonSequence.quadraticMass (PaperP1.HeterogeneousBernoulli.mean G p)
        (2*PaperP1.HeterogeneousPoissonCharlierConversion.covarianceSum E c-
          PaperP1.HeterogeneousBernoulli.powerSum G p 2) k :=
    PaperP1.AtomicSignedLaw.ofSequence_singleton (PaperP1.PoissonSequence.hasSum_quadraticMass _ _ hμ).summable k
  have h := PaperP1.UniversalHeterogeneousConversion.actual_signed_measure_conversion G E p c hE hp hP hcap
  simp only [_root_.sub_apply,PaperP1.FiniteLawEmbedding.embed_singleton,href] at h
  simpa only [finiteReference_eq,quadraticMass_eq,PaperP1.HeterogeneousBernoulli.mean,
    PaperP1.HeterogeneousBernoulli.powerSum,PaperP1.HeterogeneousPoissonCharlierConversion.covarianceSum,
    PaperP1.HeterogeneousPoissonCharlierConversion.absolutePairMass,
    PaperP1.UniversalHeterogeneousConversion.universalConstant] using h

theorem run_conversion (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑' k : ℕ, |(pairReference N L).coeff k-
        quadraticMass (actualMean N L) (secondCumulant N L) k|) ≤ (N : ℝ)^(-5/3+ε) := by
  obtain ⟨N₀,hN₀,h⟩ := PaperP1.RunConversion.main_15_1 C ε hε
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband
  have hμ : 0 ≤ PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1 := by
    rw [← actualMean_eq]; unfold actualMean moment
    exact integral_nonneg fun ω ↦ pow_nonneg (Nat.cast_nonneg (runCount N L ω)) 1
  have href (k : ℕ) : PaperP1.QuadraticPoisson.reference
      (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1)
      (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L) {k}=
      PaperP1.PoissonSequence.quadraticMass
        (PaperP1.CountObservables.countMoment (PaperP1.Model.dyadicBlock N) L 1)
        (PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L) k :=
    PaperP1.AtomicSignedLaw.ofSequence_singleton (PaperP1.PoissonSequence.hasSum_quadraticMass _ _ hμ).summable k
  simpa only [_root_.sub_apply,PaperP1.FiniteLawEmbedding.embed_singleton,href,
    pairReference_eq,quadraticMass_eq,actualMean_eq,second_eq] using
    h N hN L hband (PaperP1.Model.dyadicBlock N) Subset.rfl

theorem conditional_transfer (C β ε : ℝ) (hβ : 1 < β) (hβcap : β ≤ 4/3) (hε : 0 < ε)
    (hfixed : FixedActivity C β) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → quadraticError N L ≤ (N : ℝ)^(-β+ε) := by
  obtain ⟨N₀,hN₀,h⟩ := PaperP1.FiniteCompleteLawTransfer.article_15_13 C β ε hβ hβcap hε hfixed
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband
  rw [error_eq]
  exact h N hN L hband

theorem triple_reconstruction (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      quadraticError N L ≤ (N : ℝ)^ε*
        (∑ I ∈ (Ico N (2*N)).powersetCard 3, |centeredCoefficient L I|)+(N : ℝ)^(-4/3+ε) ∧
      quadraticError N L ≤ (N : ℝ)^(-4/3+ε) := by
  simpa only [error_eq,PaperP1.OptimalQuadratic.error,PaperP1.OptimalQuadratic.reference,
    PaperP1.CompatibleActivitySplit.absolute,PaperP1.Model.dyadicBlock,centeredCoefficient_eq] using
    PaperP1.OptimalTripleReconstruction.article_15_14 C ε hε

end PaperP1Registry.V2.StoppingReconstruction
