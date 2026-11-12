module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import PaperP1.Asymptotics.CompletePairProfile
public import PaperP1.Asymptotics.ExplicitQuadraticApproximation
public import PaperP1.Asymptotics.FixedHeightHierarchy
public import PaperP1.Asymptotics.WeightedNonalignedPairs
public import PaperP1.Asymptotics.TwoChannelReference
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

/-! # P1 V2: Arithmetic pair profiles and every fixed finite channel height

Selected statements cover main article results 3.1–3.2,8.1–8.3. Literal definitions specify
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

namespace PaperP1Registry.V2.PairsChannels

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

def pairLoss (x y L : ℕ) : ℕ := 2*L-Module.finrank F₂ (space x L⊔space y L : Submodule F₂ (ℕ →₀ F₂))

def eta (x y L : ℕ) : ℕ := if 0<jointMoment L {x,y} then 1 else 0

def signedWeight (x y L : ℕ) : ℝ := (eta x y L : ℝ)*(2^pairLoss x y L : ℝ)-1

def separatedPairs (N L : ℕ) : Finset (ℕ×ℕ) :=
  ((Ico N (2*N)) ×ˢ (Ico N (2*N))).filter fun p ↦ p.1+L<p.2 ∨ p.2+L<p.1

def regularStarts (N L : ℕ) : Finset ℕ :=
  (Ico N (2*N)).filter fun x ↦ Module.finrank F₂ (space x L)=L

def Aligned (X z L : ℕ) : Prop :=
  ∃ r s : ℕ, 0<r ∧ 0<s ∧ r.Coprime s ∧ r≤(L+1)^3 ∧ s≤(L+1)^3 ∧
    |(r : ℤ)*z-(s : ℤ)*X| ≤ ((r+s : ℕ) : ℤ)*((1*(L+1) : ℕ) : ℤ)

def regularNonalignedPairs (N L : ℕ) : Finset (ℕ×ℕ) :=
  ((regularStarts N L) ×ˢ (regularStarts N L)).filter fun p ↦
    (L : ℤ) < |(p.1 : ℤ)-p.2| ∧ ¬Aligned p.1 p.2 L

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

theorem pairLoss_eq (x y L : ℕ) : pairLoss x y L=PaperP1.NormalizedPairRankLoss.pairLoss x y L := by rfl

theorem signedWeight_eq (x y L : ℕ) : signedWeight x y L=PaperP1.SourcePairAffineWeight.signedWeight x y L := by rfl

theorem separatedPairs_eq (N L : ℕ) : separatedPairs N L=
    PaperP1.PairSeparation.separatedHosts (PaperP1.Model.dyadicBlock N) L := by
  ext p
  simp only [separatedPairs,mem_filter,mem_product,PaperP1.PairSeparation.mem_separatedHosts,
    PaperP1.Model.dyadicBlock,and_assoc]

theorem regularNonaligned_eq (N L : ℕ) : regularNonalignedPairs N L=PaperP1.WeightedNonalignedPairs.regularPairs N L := by rfl

theorem complete_pair_profile (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      |(∑ p ∈ separatedPairs N L, ((2^pairLoss p.1 p.2 L : ℝ)-1))-
        (N : ℝ)/3*((unsignedChannel L 2 3 : ℝ)+(unsignedChannel L 3 4 : ℝ))| ≤ (N : ℝ)^(6/5+ε) ∧
      |(∑ p ∈ separatedPairs N L, signedWeight p.1 p.2 L)-
        (N : ℝ)/3*((signedChannel L 2 3 : ℝ)+(signedChannel L 3 4 : ℝ))| ≤ (N : ℝ)^(6/5+ε) ∧
      |secondCumulant N L-twoChannelCoefficient N L| ≤ (N : ℝ)^(-4/5+ε) ∧
      (0<phaseMass N L 3 ∧ 0<phaseMass N L 4 ∧
        |secondCumulant N L/phaseMass N L 3-1| ≤ ε ∧
        |(secondCumulant N L-((2^L : ℝ)⁻¹)^2*((N : ℝ)*(1/3)*(signedChannel L 2 3 : ℝ)))/
          phaseMass N L 4-1| ≤ ε) := by
  simpa only [separatedPairs_eq,pairLoss_eq,signedWeight_eq,unsignedChannel_eq,signedChannel_eq,
    second_eq,twoChannel_eq,PaperP1.FiniteChannelHierarchy.twoChannelCoefficient,nominalMean_eq,
    phaseMass_eq,PaperP1.PositiveSeparatedSourceProfile.mainTerm,PaperP1.SignedSourceProfile.mainTerm,
    Int.cast_add,PaperP1.ActualPairPhase.alpha_eq_cumulant,
    PaperP1.ChannelMainTermBounds.mainTerm,
    show (PaperP1.ActualSourceTranslations.coefficient 2 3 : ℝ)=1/3 by norm_num [PaperP1.ActualSourceTranslations.coefficient]] using
    PaperP1.CompletePairProfile.main_3_3 C ε hε

theorem explicit_two_channel (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      distance (sourceSigned N L) (signedReference (nominalMean N L) (twoChannelCoefficient N L)) ≤
        (N : ℝ)^(-4/5+ε) ∧
      (∃ Q : ProbabilityMeasure ℕ, (Q : Measure ℕ).toSignedMeasure=
        signedReference (nominalMean N L) (twoChannelCoefficient N L)) ∧
      ∀ k : ℕ, signedReference (nominalMean N L) (twoChannelCoefficient N L) {k}=
        Real.exp (-nominalMean N L)*(nominalMean N L)^k/(k.factorial : ℝ)*
          (1+twoChannelCoefficient N L/2*((k : ℝ)*((k : ℝ)-1)/(nominalMean N L)^2-
            2*(k : ℝ)/nominalMean N L+1)) := by
  simpa only [distance_eq,sourceSigned_eq,signedReference_eq,nominalMean_eq,twoChannel_eq,
    PaperP1.AtomicSignedLaw.IsProbability] using PaperP1.ExplicitQuadraticApproximation.article_1_4 C ε hε

theorem fixed_height_hierarchy (h : ℕ) (hh : 3 ≤ h) (C ε : ℝ) (hε : 0 < ε) :
    ∀ τ : ℝ, 0<τ → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      |secondCumulant N L-coefficient N L h-heightMass N L (h+1)| ≤
        (N : ℝ)^(-((h+1 : ℕ) : ℝ)/((h+2 : ℕ) : ℝ)+ε) ∧
      distance (sourceSigned N L-signedReference (nominalMean N L) (coefficient N L h))
        ((heightMass N L (h+1)/2) • secondDifference (nominalMean N L)) ≤
        (N : ℝ)^(-((h+1 : ℕ) : ℝ)/((h+2 : ℕ) : ℝ)+ε) ∧
      ∃ Q : ProbabilityMeasure ℕ,
        (Q : Measure ℕ).toSignedMeasure=signedReference (nominalMean N L) (coefficient N L h) ∧
        0<leadingGap N L h ∧
        |totalVariation N L Q/(phaseMass N L (h+1)*secondNorm (nominalMean N L)/4)-1| ≤ τ := by
  simpa only [second_eq,coefficient_eq,heightMass_eq,distance_eq,sourceSigned_eq,signedReference_eq,
    nominalMean_eq,secondDifference_eq,leadingGap_eq,totalVariation_eq,phaseMass_eq,secondNorm_eq] using
    PaperP1.FixedHeightHierarchy.article_18_1 h hh C ε hε

theorem phase_positive (b r : ℕ) (hb : 3 ≤ b) : 0<phaseConstant b r := by
  exact PaperP1.ChannelPhaseConstants.phaseConstant_pos b r hb

theorem weighted_nonaligned (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑ p ∈ regularNonalignedPairs N L, ((2^relativeNullity L {p.1,p.2} : ℝ)-1)) ≤ (N : ℝ)^(1+ε) ∧
      (∑ p ∈ regularNonalignedPairs N L,
        |jointMoment L {p.1,p.2}-marginal p.1 L*marginal p.2 L|) ≤ (N : ℝ)^(-1+ε) := by
  simpa only [regularNonaligned_eq,relativeNullity_eq,jointMoment_eq,marginal_eq] using
    PaperP1.WeightedNonalignedPairs.article_18_2 C ε hε

theorem two_channel_equivalents (C : ℝ) :
    ∀ τ : ℝ, 0<τ → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∃ Q₄ Q₅ : ProbabilityMeasure ℕ,
      (Q₄ : Measure ℕ).toSignedMeasure=signedReference (nominalMean N L) (twoChannelCoefficient N L) ∧
      (Q₅ : Measure ℕ).toSignedMeasure=signedReference (nominalMean N L) (twoChannelCoefficient N L+correction N L) ∧
      0<leadingGap N L 4 ∧ 0<leadingGap N L 5 ∧
      |totalVariation N L Q₄/(17*(((L%5 : ℕ) : ℝ)+4)/(1200*(2 : ℝ)^(((L%5 : ℕ) : ℝ)/5))*
        (nominalMean N L)^(9/5 : ℝ)*secondNorm (nominalMean N L)*L*(N : ℝ)^(-4/5 : ℝ))-1| ≤ τ ∧
      |totalVariation N L Q₅/(phaseMass N L 6*secondNorm (nominalMean N L)/4)-1| ≤ τ := by
  simpa only [signedReference_eq,nominalMean_eq,twoChannel_eq,correction_eq,leadingGap_eq,
    totalVariation_eq,phaseMass_eq,secondNorm_eq] using PaperP1.TwoChannelReference.uniform_equivalents C

theorem two_channel_remainder (C ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      distance (sourceSigned N L-signedReference (nominalMean N L) (twoChannelCoefficient N L))
        ((correction N L/2) • secondDifference (nominalMean N L)) ≤ (N : ℝ)^(-5/6+ε) := by
  simpa only [distance_eq,sourceSigned_eq,signedReference_eq,nominalMean_eq,twoChannel_eq,
    correction_eq,secondDifference_eq] using PaperP1.TwoChannelReference.uniform_law_remainder C ε hε

theorem height_five_closed {N q r : ℕ} (hN : 0<N) (hq : 1≤q) (hr : r<5) :
    correction N (5*q+r)=(nominalMean N (5*q+r))^2/(30*N)*
      ((2 : ℝ)^(q-1)*(17*((r : ℝ)+4)*q+13*(r : ℝ)^2+87*r+620)-113*((5*q+r : ℕ) : ℝ)-127) := by
  simpa only [correction_eq,nominalMean_eq] using PaperP1.HeightFiveChannelCorrection.correction_closed hN hq hr

theorem height_five_coefficient (N L : ℕ) (hN : 0<N) :
    coefficient N L 4=twoChannelCoefficient N L ∧
    coefficient N L 5=twoChannelCoefficient N L+correction N L := by
  simp only [coefficient_eq,twoChannel_eq,correction_eq]
  exact ⟨PaperP1.FiniteChannelHierarchy.coefficient_four N L hN,
    (PaperP1.HeightFiveChannelCorrection.coefficient_five N L).trans
      (congrArg (fun t ↦ t+PaperP1.HeightFiveChannelCorrection.correction N L)
        (PaperP1.FiniteChannelHierarchy.coefficient_four N L hN))⟩

theorem height_six_phase (N L : ℕ) :
    phaseMass N L 6=(((L%6 : ℕ) : ℝ)+5)/(45*(2 : ℝ)^(((L%6 : ℕ) : ℝ)/6))*
      (nominalMean N L)^(11/6 : ℝ)*L*(N : ℝ)^(-5/6 : ℝ) := by
  simpa only [phaseMass_eq,nominalMean_eq] using PaperP1.TwoChannelReference.height_six_phase N L

theorem phase_three_four (r : ℕ) :
    phaseConstant 3 r=((r : ℝ)+2)/(18*(2 : ℝ)^((r : ℝ)/3)) ∧
    phaseConstant 4 r=((r : ℝ)+3)/(24*(2 : ℝ)^((r : ℝ)/4)) := by
  exact ⟨PaperP1.ChannelPhaseConstants.phaseConstant_three r,PaperP1.ChannelPhaseConstants.phaseConstant_four r⟩

theorem height_five_channels (N L : ℕ) :
    correction N L=(nominalMean N L)^2/N*
      ((2/15 : ℝ)*(signedChannel L 3 5 : ℝ)+(3/10 : ℝ)*(signedChannel L 4 5 : ℝ)) := by
  simp only [correction,heightSum_eq,signedChannel_eq,PaperP1.HeightFiveChannelCorrection.heightSum_five]

theorem fixed_height_lower_power (h : ℕ) (hh : 3≤h) (C : ℝ) :
    ∃ d : ℝ, 0<d ∧ ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      d*(N : ℝ)^(-1+1/((h+1 : ℕ) : ℝ)) ≤
        distance (sourceSigned N L) (signedReference (nominalMean N L) (coefficient N L h)) := by
  simpa only [distance_eq,sourceSigned_eq,signedReference_eq,nominalMean_eq,coefficient_eq] using
    PaperP1.FixedHeightHierarchy.uniform_lower_power h hh C

end PaperP1Registry.V2.PairsChannels
