module

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
theorem source_probability (N L : ℕ) :
    Measurable (runCount N L) ∧
    (∀ j : ℕ, Integrable (fun ω ↦ (runCount N L ω : ℝ)^j) primeSignMeasure) ∧
    (∀ k : ℕ, 0 ≤ sourceMass N L k) ∧ HasSum (sourceMass N L) 1 :=
by sorry
theorem poisson_expansion (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      |actualPoissonTV N L-secondCumulant N L/4*secondNorm (actualMean N L)| ≤
        (N : ℝ)^(-4/3+ε) ∧
      |nominalPoissonTV N L-secondCumulant N L/4*secondNorm (nominalMean N L)| ≤
        (N : ℝ)^(-1+ε) :=
by sorry
theorem moving_residue_equivalent (C : ℝ) :
    ∀ τ : ℝ, 0 < τ → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      0 < phaseScale N L ∧ |nominalPoissonTV N L/phaseScale N L-1| ≤ τ ∧
        |actualPoissonTV N L/phaseScale N L-1| ≤ τ :=
by sorry
theorem mean_bias_quantized (N L : ℕ) (hN : 2 ≤ N) (hL : 0 < L) :
    ∃ b : ℤ, actualMean N L-nominalMean N L = (2^L : ℝ)⁻¹*(b : ℝ) ∧
      (actualMean N L=nominalMean N L ∨
        (2^L : ℝ)⁻¹ ≤ |actualMean N L-nominalMean N L|) :=
by sorry
theorem nominal_quadratic_comparison (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      nominalQuadraticError N L ≤ (N : ℝ)^(-1+ε) ∧
      (actualMean N L≠nominalMean N L →
        c*|actualMean N L-nominalMean N L| ≤ nominalQuadraticError N L ∧
        nominalQuadraticError N L ≤ (6+c)*|actualMean N L-nominalMean N L|) :=
by sorry
theorem reference_series (N L : ℕ) :
    HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 ∧
    Summable (fun k : ℕ ↦ |sourceMass N L k-
      quadraticMass (actualMean N L) (secondCumulant N L) k|) :=
by sorry
theorem optimal_quadratic (C ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      a*(N : ℝ)^(-4/3-ε) ≤ quadraticError N L ∧
      quadraticError N L ≤ (N : ℝ)^(-4/3+ε) ∧
      |actualMean N L-nominalMean N L| ≤ (2 : ℝ)^C*(N : ℝ)^(-1+ε) ∧
      (∀ k : ℕ, 0 ≤ quadraticMass (actualMean N L) (secondCumulant N L) k) ∧
      HasSum (quadraticMass (actualMean N L) (secondCumulant N L)) 1 :=
by sorry
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
      factorialMoment N L 2=(actualMean N L)^2+secondCumulant N L :=
by sorry
theorem no_retained_start (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      |sourceMass N L 0-Real.exp (-actualMean N L)*(1+secondCumulant N L/2)| ≤
        (N : ℝ)^(-4/3+ε) :=
by sorry
theorem literal_mean_bias (N L : ℕ) (hN : 2≤N) (hL : 0<L) :
    actualMean N L-nominalMean N L=(2^L : ℝ)⁻¹*(integerBias N L : ℝ) ∧
    ∀ C : ℝ, |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ((2 : ℝ)^C)⁻¹/N ≤ (2^L : ℝ)⁻¹ ∧ (2^L : ℝ)⁻¹ ≤ (2 : ℝ)^C/N :=
by sorry

end PaperP1Registry.V2.QuadraticLimits
