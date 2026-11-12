module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic

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
theorem quadratic_probability_criterion (μ α : ℝ) (hμ : 0<μ) :
    ((∀ k : ℕ, 0≤quadraticMass μ α k) ∧ HasSum (quadraticMass μ α) 1) ↔
      0≤α ∧ α≤2*μ^2/(μ+fractionalPart μ*(1-fractionalPart μ)) :=
by sorry
theorem quadratic_mass_formula (μ α : ℝ) (hμ : 0<μ) (k : ℕ) :
    signedReference μ α {k}=Real.exp (-μ)*μ^k/(k.factorial : ℝ)*
      (1+α/(2*μ^2)*(((k : ℝ)-μ)^2-k)) :=
by sorry
theorem hermite_exact (C ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, 10≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤secondCumulant N L, ∃ hαμ : secondCumulant N L≤actualMean N L,
      distance (sourceSigned N L)
        (hermiteLaw (actualMean N L) (secondCumulant N L) hα hαμ : Measure ℕ).toSignedMeasure ≤
          (N : ℝ)^(-4/3+ε) ∧
      totalVariation N L (hermiteLaw (actualMean N L) (secondCumulant N L) hα hαμ) ≤
        (N : ℝ)^(-4/3+ε) :=
by sorry
theorem hermite_fixed_height (h : ℕ) (hh : 3≤h) (C ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤coefficient N L h, ∃ hαμ : coefficient N L h≤nominalMean N L,
      distance (sourceSigned N L)
        (hermiteLaw (nominalMean N L) (coefficient N L h) hα hαμ : Measure ℕ).toSignedMeasure ≤
          (N : ℝ)^(-1+1/((h+1 : ℕ) : ℝ)+ε) :=
by sorry
theorem hermite_fixed_equivalent (h : ℕ) (hh : 3≤h) (C : ℝ) :
    ∀ τ : ℝ, 0<τ → ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∃ hα : 0≤coefficient N L h, ∃ hαμ : coefficient N L h≤nominalMean N L,
      0<leadingGap N L h ∧
      |totalVariation N L (hermiteLaw (nominalMean N L) (coefficient N L h) hα hαμ)/
        (phaseMass N L (h+1)*secondNorm (nominalMean N L)/4)-1| ≤ τ :=
by sorry

end PaperP1Registry.V2.ProbabilityReferences
