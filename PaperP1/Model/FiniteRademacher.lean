/-
Adapted in part from Vulkin-prog/paper-c-lean,
PaperC/Model/FiniteRademacher.lean and the StartEvent definition in
PaperC/Runs/Starts.lean, commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Apache-2.0. See docs/PAPER_C_REUSE.md for exact source identities and changes.
-/
module

public import PaperP1.Arithmetic.ParityVector
public import PaperP1.Probability.Convolution
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Finset.Interval
public import Lean.Elab.Tactic.Omega

/-!
# Finite prime-sign cylinders and run-start counts

Prime signs are represented by bits over `ZMod 2`. The uniform law on the
finite function space assigns independent fair bits to all prime coordinates
up to the cutoff. The deterministic model is completely multiplicative on
positive integers. The chosen dyadic cutoff contains every run-window vertex.

The probability measure used here is explicitly constructed from uniform
finite weights. Infinite-product measure identification is a separate step.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Probability

namespace PaperP1.Model

/-- Primes below an inclusive cutoff. -/
def PrimeUpTo (M : ℕ) := {p : Fin (M + 1) // Nat.Prime p.1}

instance (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _

instance (M : ℕ) : DecidableEq (PrimeUpTo M) := Classical.decEq _

abbrev SampleSpace (M : ℕ) := PrimeUpTo M → F₂

def valueBit {M : ℕ} (ω : SampleSpace M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parityVec n p.1

def valueLinear (M n : ℕ) : SampleSpace M →ₗ[F₂] F₂ where
  toFun := fun ω => valueBit ω n
  map_add' := by
    intro ω η
    simp [valueBit, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c ω
    simp [valueBit, Finset.mul_sum, mul_assoc]

@[simp]
theorem valueLinear_apply {M n : ℕ} (ω : SampleSpace M) :
    valueLinear M n ω = valueBit ω n := rfl

theorem valueBit_mul {M a b : ℕ} (ω : SampleSpace M) (ha : a ≠ 0) (hb : b ≠ 0) :
    valueBit ω (a * b) = valueBit ω a + valueBit ω b := by
  simp [valueBit, parityVec_mul ha hb, mul_add, Finset.sum_add_distrib]

def phase (z : F₂) : ℤ := if z = 0 then 1 else -1

@[simp]
theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_add (a b : F₂) : phase (a + b) = phase a * phase b := by
  revert a b
  decide

theorem phase_eq_iff (a b : F₂) : phase a = phase b ↔ a = b := by
  revert a b
  decide

theorem phase_eq_neg_iff (a b : F₂) : phase a = -phase b ↔ a + b = 1 := by
  revert a b
  decide

def randomMultiplicativeValue {M : ℕ} (ω : SampleSpace M) (n : ℕ) : ℤ := phase (valueBit ω n)

theorem randomMultiplicativeValue_mul {M a b : ℕ} (ω : SampleSpace M)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    randomMultiplicativeValue ω (a * b) =
      randomMultiplicativeValue ω a * randomMultiplicativeValue ω b := by
  simp only [randomMultiplicativeValue, valueBit_mul ω ha hb, phase_add]

/-- Both signs are included; the preceding value has the opposite sign. -/
def StartEvent (g : ℕ → F₂) (x L : ℕ) : Prop :=
  g (x - 1) + g x = 1 ∧ ∀ j : ℕ, j < L → g (x + j) = g x

/-- The deterministic start predicate in a finite prime-sign cylinder. -/
def startAt {M : ℕ} (ω : SampleSpace M) (x L : ℕ) : Prop :=
  StartEvent (valueBit ω) x L

theorem startEvent_iff_signed (g : ℕ → F₂) (x L : ℕ) :
    StartEvent g x L ↔
      phase (g (x - 1)) = -phase (g x) ∧
        ∀ j : ℕ, j < L → phase (g (x + j)) = phase (g x) := by
  simp only [StartEvent, phase_eq_neg_iff, phase_eq_iff]

def dyadicCutoff (N L : ℕ) : ℕ := 2 * N + L

abbrev DyadicSample (N L : ℕ) := SampleSpace (dyadicCutoff N L)

def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Ico N (2 * N)

@[simp]
theorem dyadicBlock_card (N : ℕ) : (dyadicBlock N).card = N := by
  simp [dyadicBlock, two_mul]

theorem startWindow_le_dyadicCutoff {N L x j : ℕ}
    (hx : x ∈ dyadicBlock N) (hj : j < L) : x + j ≤ dyadicCutoff N L := by
  simp only [dyadicBlock, Finset.mem_Ico] at hx
  unfold dyadicCutoff
  omega

theorem startBoundary_le_dyadicCutoff {N L x : ℕ} (hx : x ∈ dyadicBlock N) :
    x - 1 ≤ dyadicCutoff N L := by
  simp only [dyadicBlock, Finset.mem_Ico] at hx
  unfold dyadicCutoff
  omega

theorem two_le_of_mem_dyadicBlock {N x : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicBlock N) :
    2 ≤ x := by
  exact le_trans hN (Finset.mem_Ico.mp hx).1

def startIndicator {M : ℕ} (x L : ℕ) (ω : SampleSpace M) : Bool := by
  classical
  exact decide (StartEvent (valueBit ω) x L)

theorem startIndicator_eq_true_iff {M : ℕ} (x L : ℕ) (ω : SampleSpace M) :
    startIndicator x L ω = true ↔ StartEvent (valueBit ω) x L := by
  simp [startIndicator]

def cylinderProbability (M : ℕ) : FiniteProbability (SampleSpace M) :=
  uniformFiniteProbability (SampleSpace M)

def dyadicCountLaw (N L : ℕ) : SignedLaw ℝ :=
  countLaw (dyadicBlock N) (cylinderProbability (dyadicCutoff N L)).weight
    (fun x => startIndicator x L)

theorem dyadicCountLaw_isProbability (N L : ℕ) : IsProbability (dyadicCountLaw N L) :=
  countLaw_isProbability (dyadicBlock N) (cylinderProbability (dyadicCutoff N L))
    (fun x => startIndicator x L)

/-- Actual marginal probability, including every locally possible start. -/
def dyadicMarginal (N L x : ℕ) : ℝ :=
  exactMarginal (cylinderProbability (dyadicCutoff N L)) (fun y => startIndicator y L) x

def dyadicCenteredMoment (N L : ℕ) (I : Finset ℕ) : ℝ :=
  PaperP1.Algebra.centeredMoment (cylinderProbability (dyadicCutoff N L)).weight
    (fun x ω => indicatorValue (startIndicator x L ω)) (dyadicMarginal N L) I

theorem dyadicCenteredMoment_singleton (N L x : ℕ) :
    dyadicCenteredMoment N L {x} = 0 := by
  exact PaperP1.Algebra.centeredMoment_singleton_eq_zero
    (cylinderProbability (dyadicCutoff N L)).weight
    (fun i ω => indicatorValue (startIndicator i L ω)) x
    (cylinderProbability (dyadicCutoff N L)).total_weight

/-- Centered expansion in the constructed finite prime cylinder.

The manuscript's exact-marginal formula is instantiated here without replacing
any individual probability by the nominal value `2⁻ᴸ` or deleting irregular
windows. Consistency with the unrestricted prime-sign probability space is
tracked separately rather than asserted by this finite-cylinder theorem.
-/
theorem dyadic_centered_expansion (N L : ℕ) :
    dyadicCountLaw N L = ∑ I ∈ (dyadicBlock N).powerset,
      scalar (dyadicCenteredMoment N L I) * forwardDifference ^ I.card *
        ∏ x ∈ dyadicBlock N \ I, bernoulli (dyadicMarginal N L x) := by
  exact centered_countLaw_expansion (dyadicBlock N)
    (cylinderProbability (dyadicCutoff N L)).weight (fun x => startIndicator x L)
    (dyadicMarginal N L)

theorem dyadic_marginal_reference_isProbability (N L : ℕ) (I : Finset ℕ) :
    IsProbability (∏ x ∈ dyadicBlock N \ I, bernoulli (dyadicMarginal N L x)) := by
  exact exactMarginal_reference_isProbability (dyadicBlock N \ I)
    (cylinderProbability (dyadicCutoff N L)) (fun x => startIndicator x L)

end PaperP1.Model
