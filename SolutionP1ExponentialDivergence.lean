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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup
public import PaperP1.Asymptotics.PrimeCylinderLiminf
public import PaperP1.Model.OneSidedPrimeCylinder

/-! # Actual exponential-moment divergence for multiplicative run starts
The literal independent prime-sign law and actual positive/total start
counts are explicit. The finite one-sided cylinder improvement is kept
separate from the original odd-prime asymptotic regime t>2.
Prime-sign foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0;
see docs/PAPER_C_REUSE.md. Four selected Challenge holes are deliberate.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.ExponentialDivergence
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

def primeScale (q : ℕ) : ℕ := 2^(q-1)

def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹

def positiveRate (t : ℝ) (q : ℕ) : ℝ :=
  Real.log (primeScale q)/primeScale q*Real.log (positiveMGF (primeScale q) (q-1) t)

def totalRate (t : ℝ) (q : ℕ) : ℝ :=
  Real.log (primeScale q)/primeScale q*Real.log (totalMGF (primeScale q) (q-1) t)

/-- The unbounded filter of odd prime indices; nontriviality is part of the theorem. -/
def oddPrimeFilter : Filter ℕ :=
  Filter.atTop ⊓ Filter.principal {q | Nat.Prime q ∧ 2<q}

theorem count_eq (N L : ℕ) (ω : Sample) : runCount N L ω=
    PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem positiveCount_eq (N L : ℕ) (ω : Sample) : positiveCount N L ω=
    PaperP1.PositiveStarts.infiniteCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem positiveMGF_eq (N L : ℕ) (t : ℝ) : positiveMGF N L t=
    PaperP1.PositiveStarts.exponentialMoment (PaperP1.Model.dyadicBlock N) L t := by rfl

theorem totalMGF_eq (N L : ℕ) (t : ℝ) : totalMGF N L t=
    PaperP1.PrimeRunCylinder.totalExponentialMoment N L t := by rfl

theorem primeScale_eq (q : ℕ) : primeScale q=PaperP1.PrimeCylinderScale.size q := by rfl

theorem positiveRate_eq (t : ℝ) (q : ℕ) : positiveRate t q=
    PaperP1.PrimeCylinderDivergence.positiveRate t q := by rfl

theorem totalRate_eq (t : ℝ) (q : ℕ) : totalRate t q=
    PaperP1.PrimeCylinderDivergence.totalRate t q := by rfl

theorem oddPrimeFilter_eq : oddPrimeFilter=PaperP1.PrimeCylinderLiminf.oddPrimeIndices := by rfl

theorem cylinder_integrable (M : ℕ) (f : PaperP1.Model.SampleSpace M → ℝ) :
    Integrable (fun ω ↦ f (PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M ω))
      primeSignMeasure := by
  change Integrable (f ∘ PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M)
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure
  exact (PaperP1.Probability.integrable_finite_function
    (PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure.map
      (PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M)) f).comp_measurable
        (PaperP1.Probability.CylinderExpectations.measurable_restrictToFinite M)

theorem positive_integrable (N L : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t*(positiveCount N L ω : ℝ))) primeSignMeasure := by
  let M := PaperP1.Model.dyadicCutoff N L
  let f : PaperP1.Model.SampleSpace M → ℝ := fun σ ↦ Real.exp (t*
    (PaperP1.Probability.indicatorCount (PaperP1.Model.dyadicBlock N)
      (fun x ↦ PaperP1.PositiveStarts.indicator x L) σ : ℝ))
  have h := cylinder_integrable M f
  have heq : (fun ω ↦ Real.exp (t*(positiveCount N L ω : ℝ)))=
      (fun ω ↦ f (PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M ω)) := by
    funext ω
    dsimp [f]
    rw [PaperP1.PositiveStarts.count_restrict _ _ _
      (PaperP1.CountObservables.dyadic_subset_cutoff (subset_refl _))]
    rfl
  rw [heq]
  exact h

theorem total_integrable (N L : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t*(runCount N L ω : ℝ))) primeSignMeasure := by
  let M := PaperP1.Model.dyadicCutoff N L
  let f : PaperP1.Model.SampleSpace M → ℝ := fun σ ↦ Real.exp (t*
    (PaperP1.Probability.indicatorCount (PaperP1.Model.dyadicBlock N)
      (fun x ↦ PaperP1.Model.startIndicator x L) σ : ℝ))
  have h := cylinder_integrable M f
  have heq : (fun ω ↦ Real.exp (t*(runCount N L ω : ℝ)))=
      (fun ω ↦ f (PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M ω)) := by
    funext ω
    dsimp [f]
    rw [PaperP1.Model.InfiniteStarts.infiniteStartCount_restrict _ _ _
      (PaperP1.CountObservables.dyadic_subset_cutoff (subset_refl _))]
    rfl
  rw [heq]
  exact h

theorem nominalMean_one (q : ℕ) : nominalMean (primeScale q) (q-1)=1 := by
  simp only [nominalMean, primeScale, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))

/-- Explicit integrability and a sharper finite lower bound under the actual law. -/
theorem finite_cylinder_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Integrable (fun ω ↦ Real.exp (t*(positiveCount N (q-1) ω : ℝ))) primeSignMeasure ∧
    Integrable (fun ω ↦ Real.exp (t*(runCount N (q-1) ω : ℝ))) primeSignMeasure ∧
    0<positiveMGF N (q-1) t ∧ positiveMGF N (q-1) t≤totalMGF N (q-1) t ∧
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (Nat.primeCounting (2*N+(q-1)) : ℝ)*Real.log 2)≤positiveMGF N (q-1) t ∧
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (Nat.primeCounting (2*N+(q-1)) : ℝ)*Real.log 2)≤totalMGF N (q-1) t := by
  have hpos : Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (Nat.primeCounting (2*N+(q-1)) : ℝ)*Real.log 2)≤positiveMGF N (q-1) t := by
    simpa only [positiveMGF_eq, PaperP1.Model.dyadicCutoff,
      PaperP1.LocalRigidityCode.primeCount_eq_primeCounting] using
        PaperP1.OneSidedPrimeCylinder.positive_exponential_lower hq hqN t ht
  have horder : positiveMGF N (q-1) t≤totalMGF N (q-1) t :=
    PaperP1.PrimeRunCylinder.positive_le_total N (q-1) t ht
  exact ⟨positive_integrable N (q-1) t, total_integrable N (q-1) t,
    (Real.exp_pos _).trans_le hpos, horder, hpos, hpos.trans horder⟩

/-- A single threshold precedes all prime indices for both scaled logarithms. -/
theorem prime_threshold_bounds (t : ℝ) (ht : 2<t) :
    0<(t-2)*Real.log 2 ∧ ∀ ε : ℝ, 0<ε → ∃ q₀ : ℕ, 3≤q₀ ∧
      ∀ q : ℕ, q₀≤q → Nat.Prime q →
        (t-2)*Real.log 2-ε≤positiveRate t q ∧
        (t-2)*Real.log 2-ε≤totalRate t q := by
  exact PaperP1.PrimeCylinderDivergence.companion_T19_7 t ht

/-- Literal extended-real lower limits along a nontrivial odd-prime filter. -/
theorem odd_prime_liminf (t : ℝ) (ht : 2<t) :
    Filter.NeBot oddPrimeFilter ∧ (0 : EReal)<((t-2)*Real.log 2 : ℝ) ∧
      (((t-2)*Real.log 2 : ℝ) : EReal)≤
        Filter.liminf (fun q ↦ (positiveRate t q : EReal)) oddPrimeFilter ∧
      (((t-2)*Real.log 2 : ℝ) : EReal)≤
        Filter.liminf (fun q ↦ (totalRate t q : EReal)) oddPrimeFilter := by
  exact ⟨PaperP1.PrimeCylinderLiminf.oddPrimeIndices_neBot,
    PaperP1.PrimeCylinderLiminf.companion_T19_7_liminf t ht⟩

/-- Both logarithms and both actual moments diverge, at nominal mean exactly one. -/
theorem logarithms_and_moments_diverge (t : ℝ) (ht : 2<t) (K : ℝ) :
    ∃ q₀ : ℕ, 3≤q₀ ∧ ∀ q : ℕ, q₀≤q → Nat.Prime q →
      nominalMean (primeScale q) (q-1)=1 ∧
      K≤Real.log (positiveMGF (primeScale q) (q-1) t) ∧
      K≤Real.log (totalMGF (primeScale q) (q-1) t) ∧
      K≤positiveMGF (primeScale q) (q-1) t ∧
      K≤totalMGF (primeScale q) (q-1) t := by
  obtain ⟨qLog, hLog3, hLog⟩ := PaperP1.PrimeCylinderDivergence.logarithms_diverge t ht K
  obtain ⟨qMoment, hMoment3, hMoment⟩ := PaperP1.PrimeCylinderDivergence.moments_diverge t ht K
  refine ⟨max qLog qMoment, hLog3.trans (le_max_left _ _), fun q hq hprime ↦ ?_⟩
  obtain ⟨hpl, htl⟩ := hLog q ((le_max_left _ _).trans hq) hprime
  obtain ⟨hpm, htm⟩ := hMoment q ((le_max_right _ _).trans hq) hprime
  exact ⟨nominalMean_one q, hpl, htl, hpm, htm⟩
end PaperP1Registry.ExponentialDivergence
