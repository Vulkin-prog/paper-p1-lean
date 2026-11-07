module

public import Mathlib.Data.Nat.Log
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

/-! # Finite valuation cylinders and their actual affine forcing cost
The independent prime-sign law, actual counts, complete retained set and
finite forcing map are explicit Mathlib-only definitions. Four selected
statements cover finite layers, uniform density, exact forcing mass and
rank-charged actual moments, and the five-start factor-two example.
Prime-sign foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0;
see docs/PAPER_C_REUSE.md. Four selected Challenge holes are deliberate.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.PrimeCylinders
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

/-- Starts whose constant word has positive sign; the preceding sign is negative. -/
def positiveIndicator (x L : ℕ) (ω : Sample) : Bool :=
  startIndicator x L ω && decide (valueBit ω x=0)

def positiveCount (N L : ℕ) (ω : Sample) : ℕ :=
  ∑ x ∈ Ico N (2*N), (positiveIndicator x L ω).toNat

def positiveMGF (N L : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t*(positiveCount N L ω : ℝ)) ∂primeSignMeasure

def totalMGF (N L : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t*(runCount N L ω : ℝ)) ∂primeSignMeasure

def cutoff (N q : ℕ) : ℕ := 2*q*(N/q)

def retainedParameters (N q : ℕ) : Finset ℕ :=
  (Ico (N/q+1) (N/q+1+(N/q-1))).filter fun u ↦ Even (u.factorization q)

def retainedStarts (N q : ℕ) : Finset ℕ := (retainedParameters N q).image fun u ↦ q*u+1

def retainedCount (N q : ℕ) : ℕ := (retainedStarts N q).card

def layerBudget (N q k : ℕ) : ℝ :=
  (N : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k))-3*(k : ℝ)

def depth (N q : ℕ) : ℕ := (Nat.clog q N+1)/2

def FinitePrime (M : ℕ) := {p : Fin (M+1) // Nat.Prime p.val}
instance finitePrimeFintype (M : ℕ) : Fintype (FinitePrime M) := Subtype.fintype _
instance finitePrimeDecidableEq (M : ℕ) : DecidableEq (FinitePrime M) := Classical.decEq _
abbrev FiniteSample (M : ℕ) := FinitePrime M → F₂

def finiteValueBit {M : ℕ} (σ : FiniteSample M) (n : ℕ) : F₂ :=
  ∑ p : FinitePrime M, σ p*parity n p.val.val

def finiteValueLinear (M n : ℕ) : FiniteSample M →ₗ[F₂] F₂ where
  toFun σ := finiteValueBit σ n
  map_add' := by
    intro σ τ
    simp [finiteValueBit,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro c σ
    simp [finiteValueBit,Finset.mul_sum,mul_assoc]

def forcingRow (M x L : ℕ) (i : Option (Fin L)) : FiniteSample M →ₗ[F₂] F₂ :=
  match i with
  | none => finiteValueLinear M (x-1)
  | some j => finiteValueLinear M (x+j.val)

def forcingSystem (M : ℕ) (G : Finset ℕ) (L : ℕ) :
    FiniteSample M →ₗ[F₂] (↥G × Option (Fin L) → F₂) :=
  LinearMap.pi fun i ↦ forcingRow M i.1.val L i.2

def forcingRhs (G : Finset ℕ) (L : ℕ) : ↥G × Option (Fin L) → F₂ :=
  fun i ↦ match i.2 with | none => 1 | some _ => 0

def forcingRank (N q : ℕ) : ℕ :=
  Module.finrank F₂ (LinearMap.range (forcingSystem (cutoff N q) (retainedStarts N q) (q-1)))

/-- Actual normalized cardinality of the forcing event under the fair finite prime-bit law. -/
def forcingMass (N q : ℕ) : ℝ :=
  (Nat.card {σ : FiniteSample (cutoff N q) //
    forcingSystem (cutoff N q) (retainedStarts N q) (q-1) σ=
      forcingRhs (retainedStarts N q) (q-1)} : ℝ)/(Nat.card (FiniteSample (cutoff N q)) : ℝ)

/-- Explicit finite-layer count and both actual full moment bounds. -/
theorem finite_valuation_cylinders {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (k : ℕ) (t : ℝ) (ht : 0≤t) :
    layerBudget N q k≤(retainedCount N q : ℝ) ∧
    Real.exp (t*layerBudget N q k-(Nat.primeCounting (cutoff N q) : ℝ)*Real.log 2)≤
      positiveMGF N (q-1) t ∧
    Real.exp (t*layerBudget N q k-(Nat.primeCounting (cutoff N q) : ℝ)*Real.log 2)≤
      totalMGF N (q-1) t := by
  sorry

/-- Complete finite cover, fixed-prime density and a threshold independent of the prime. -/
theorem effective_retained_density :
    (∀ N q : ℕ, Nat.Prime q → q≤N →
      ((N : ℝ)-1)/((q : ℝ)+1)-3*(depth N q : ℝ)≤(retainedCount N q : ℝ) ∧
      (retainedCount N q : ℝ)≤(N : ℝ)/((q : ℝ)+1)+2*(depth N q : ℝ)) ∧
    (∀ q : ℕ, Nat.Prime q → Filter.Tendsto
      (fun N : ℕ ↦ (retainedCount N q : ℝ)/(N : ℝ)) Filter.atTop (nhds (1/((q : ℝ)+1)))) ∧
    ∀ ε : ℝ, 0<ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N → ∀ q : ℕ, Nat.Prime q → q≤N →
      |(retainedCount N q : ℝ)/(N : ℝ)-1/((q : ℝ)+1)|≤ε := by
  sorry

/-- Exact actual forcing probability, effective rank and both full-model moment bounds. -/
theorem rank_charged_moments {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    forcingMass N q=(2^forcingRank N q : ℝ)⁻¹ ∧
    forcingRank N q≤Nat.primeCounting (cutoff N q) ∧
    Real.exp (t*(retainedCount N q : ℝ)-(forcingRank N q : ℝ)*Real.log 2)≤positiveMGF N (q-1) t ∧
    Real.exp (t*(retainedCount N q : ℝ)-(forcingRank N q : ℝ)*Real.log 2)≤totalMGF N (q-1) t := by
  sorry

/-- A nonempty exact finite example with at least a factor-two probability gain. -/
theorem five_start_gain :
    retainedCount 18 3=5 ∧ forcingRank 18 3≤10 ∧ Nat.primeCounting 36=11 ∧
    ∀ t : ℝ, 0≤t →
      Real.exp (5*t-10*Real.log 2)≤positiveMGF 18 2 t ∧
      Real.exp (5*t-10*Real.log 2)≤totalMGF 18 2 t := by
  sorry
end PaperP1Registry.PrimeCylinders
