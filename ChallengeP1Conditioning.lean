module

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
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Actual conditional laws and colored replica target sums
The independent prime-sign law, literal run bits, joint probabilities and
shared-small-prime colored replicas are explicit. All thresholds precede the
moving scales and all source prescriptions. The source count remains fixed.
Selected model foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the four selected Challenge theorem holes are deliberate placeholders.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.Conditioning
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

/-- Actual relative window bits; row zero is the preceding boundary equation. -/
def startBits (x L : ℕ) (ω : Sample) (i : Fin L) : F₂ :=
  if i.val=0 then valueBit ω (x-1)+valueBit ω x else valueBit ω x+valueBit ω (x+i.val)

def sourceEvent {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂) (ω : Sample) : Prop :=
  ∀ i, startBits (x i) L ω=b i

/-- Literal conditional probability, with the actual joint mass denominator. -/
def conditionalProbability {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (b : Fin s → Fin L → F₂)
    (z : ℕ) (c : Fin L → F₂) : ℝ :=
  primeSignMeasure.real {ω | sourceEvent x L b ω ∧ startBits z L ω=c}/
    primeSignMeasure.real {ω | sourceEvent x L b ω}

def jointStarts (A : Finset ℕ) (L : ℕ) : Set Sample :=
  {ω | ∀ x ∈ A, StartEvent (valueBit ω) x L}

def jointMass (A : Finset ℕ) (L : ℕ) : ℝ := primeSignMeasure.real (jointStarts A L)

def conditionalStart (A : Finset ℕ) (L z : ℕ) : ℝ := jointMass (insert z A) L/jointMass A L

def negativeDeviation (N L : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ z ∈ Ico N (2*N) \ A, max 0 ((2^L : ℝ)⁻¹-conditionalStart A L z)

/-- One common sign sample and independently colored fresh samples. -/
abbrev ColoredSample (κ : Type*) := Sample × (κ → Sample)

def coloredMeasure (κ : Type*) [Fintype κ] : Measure (ColoredSample κ) :=
  primeSignMeasure.prod (Measure.pi (fun _ : κ ↦ primeSignMeasure))

instance coloredProbability (κ : Type*) [Fintype κ] : IsProbabilityMeasure (coloredMeasure κ) := by
  unfold coloredMeasure
  infer_instance

/-- All primes at most Y use the common sample; larger primes use the indicated color. -/
def selected {κ : Type*} (Y : ℕ) (k : κ) (ω : ColoredSample κ) : Sample :=
  fun j ↦ if Nat.nth Nat.Prime j ≤ Y then ω.1 j else ω.2 k j

def coloredBits {κ : Type*} (Y x L : ℕ) (k : κ) (ω : ColoredSample κ) : Fin L → F₂ :=
  startBits x L (selected Y k ω)

def coloredSourceEvent {κ : Type*} {s : ℕ} (Y L : ℕ) (x : Fin s → ℕ)
    (color : Option (Fin s) → κ) (b : Fin s → Fin L → F₂) (ω : ColoredSample κ) : Prop :=
  ∀ i, coloredBits Y (x i) L (color (some i)) ω=b i

def coloredConditionalProbability {κ : Type*} [Fintype κ] {s : ℕ} (Y L : ℕ)
    (x : Fin s → ℕ) (z : ℕ) (color : Option (Fin s) → κ)
    (b : Fin s → Fin L → F₂) (c : Fin L → F₂) : ℝ :=
  (coloredMeasure κ).real {ω | coloredSourceEvent Y L x color b ω ∧ coloredBits Y z L (color none) ω=c}/
    (coloredMeasure κ).real {ω | coloredSourceEvent Y L x color b ω}

/-- Uniform conditional target sum for all compatible source prescriptions
and arbitrary target prescriptions, even depending on the target centre. -/
theorem conditional_target_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2*N)) →
      ∀ b : Fin s → Fin L → F₂,
        0 < primeSignMeasure.real {ω | sourceEvent x L b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2*N), conditionalProbability x L b z (c z)) ≤ (N : ℝ)^ε :=
by sorry

/-- The same cutoff works for every finite replica color set, every shared
small-prime cutoff and every color assignment, after conditioning on the actual
positive joint source probability. The number of sources s remains fixed. -/
theorem colored_target_sum (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2*N)) →
      ∀ (κ : Type*) [Fintype κ], ∀ Y : ℕ, ∀ color : Option (Fin s) → κ,
      ∀ b : Fin s → Fin L → F₂,
        0 < (coloredMeasure κ).real {ω | coloredSourceEvent Y L x color b ω} →
      ∀ c : ℕ → Fin L → F₂,
        (∑ z ∈ Ico N (2*N), coloredConditionalProbability Y L x z color b (c z)) ≤ (N : ℝ)^ε :=
by sorry

/-- Actual negative conditional deviation after any fixed number of starts.
All source sets and every positive actual joint conditioning event are uniform. -/
theorem negative_deviation (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ Ico N (2*N) → A.card ≤ j → 0 < jointMass A L →
      negativeDeviation N L A ≤ (N : ℝ)^(-1/2+ε) :=
by sorry

/-- Conditional mean of the literal full count after removing the prescribed
source starts, with its actual probability denominator retained. -/
theorem conditional_mean_lower (C : ℝ) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C → ∀ A : Finset ℕ,
      A ⊆ Ico N (2*N) → A.card ≤ j → 0 < jointMass A L →
      (N : ℝ)*(2^L : ℝ)⁻¹-(N : ℝ)^(-1/2+ε) ≤
        (∫ ω, if ω ∈ jointStarts A L then (runCount N L ω : ℝ)-(A.card : ℝ) else 0 ∂primeSignMeasure)/
          jointMass A L :=
by sorry

end PaperP1Registry.Conditioning
