module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

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
          phaseMass N L 4-1| ≤ ε) :=
by sorry
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
            2*(k : ℝ)/nominalMean N L+1)) :=
by sorry
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
        |totalVariation N L Q/(phaseMass N L (h+1)*secondNorm (nominalMean N L)/4)-1| ≤ τ :=
by sorry
theorem phase_positive (b r : ℕ) (hb : 3 ≤ b) : 0<phaseConstant b r :=
by sorry
theorem weighted_nonaligned (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      (∑ p ∈ regularNonalignedPairs N L, ((2^relativeNullity L {p.1,p.2} : ℝ)-1)) ≤ (N : ℝ)^(1+ε) ∧
      (∑ p ∈ regularNonalignedPairs N L,
        |jointMoment L {p.1,p.2}-marginal p.1 L*marginal p.2 L|) ≤ (N : ℝ)^(-1+ε) :=
by sorry
theorem two_channel_equivalents (C : ℝ) :
    ∀ τ : ℝ, 0<τ → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∃ Q₄ Q₅ : ProbabilityMeasure ℕ,
      (Q₄ : Measure ℕ).toSignedMeasure=signedReference (nominalMean N L) (twoChannelCoefficient N L) ∧
      (Q₅ : Measure ℕ).toSignedMeasure=signedReference (nominalMean N L) (twoChannelCoefficient N L+correction N L) ∧
      0<leadingGap N L 4 ∧ 0<leadingGap N L 5 ∧
      |totalVariation N L Q₄/(17*(((L%5 : ℕ) : ℝ)+4)/(1200*(2 : ℝ)^(((L%5 : ℕ) : ℝ)/5))*
        (nominalMean N L)^(9/5 : ℝ)*secondNorm (nominalMean N L)*L*(N : ℝ)^(-4/5 : ℝ))-1| ≤ τ ∧
      |totalVariation N L Q₅/(phaseMass N L 6*secondNorm (nominalMean N L)/4)-1| ≤ τ :=
by sorry
theorem two_channel_remainder (C ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      distance (sourceSigned N L-signedReference (nominalMean N L) (twoChannelCoefficient N L))
        ((correction N L/2) • secondDifference (nominalMean N L)) ≤ (N : ℝ)^(-5/6+ε) :=
by sorry
theorem height_five_closed {N q r : ℕ} (hN : 0<N) (hq : 1≤q) (hr : r<5) :
    correction N (5*q+r)=(nominalMean N (5*q+r))^2/(30*N)*
      ((2 : ℝ)^(q-1)*(17*((r : ℝ)+4)*q+13*(r : ℝ)^2+87*r+620)-113*((5*q+r : ℕ) : ℝ)-127) :=
by sorry
theorem height_five_coefficient (N L : ℕ) (hN : 0<N) :
    coefficient N L 4=twoChannelCoefficient N L ∧
    coefficient N L 5=twoChannelCoefficient N L+correction N L :=
by sorry
theorem height_six_phase (N L : ℕ) :
    phaseMass N L 6=(((L%6 : ℕ) : ℝ)+5)/(45*(2 : ℝ)^(((L%6 : ℕ) : ℝ)/6))*
      (nominalMean N L)^(11/6 : ℝ)*L*(N : ℝ)^(-5/6 : ℝ) :=
by sorry
theorem phase_three_four (r : ℕ) :
    phaseConstant 3 r=((r : ℝ)+2)/(18*(2 : ℝ)^((r : ℝ)/3)) ∧
    phaseConstant 4 r=((r : ℝ)+3)/(24*(2 : ℝ)^((r : ℝ)/4)) :=
by sorry
theorem height_five_channels (N L : ℕ) :
    correction N L=(nominalMean N L)^2/N*
      ((2/15 : ℝ)*(signedChannel L 3 5 : ℝ)+(3/10 : ℝ)*(signedChannel L 4 5 : ℝ)) :=
by sorry
theorem fixed_height_lower_power (h : ℕ) (hh : 3≤h) (C : ℝ) :
    ∃ d : ℝ, 0<d ∧ ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      d*(N : ℝ)^(-1+1/((h+1 : ℕ) : ℝ)) ≤
        distance (sourceSigned N L) (signedReference (nominalMean N L) (coefficient N L h)) :=
by sorry

end PaperP1Registry.V2.PairsChannels
