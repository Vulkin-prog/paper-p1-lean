module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup
public import PaperP1.Asymptotics.PrimeCylinderLiminf
public import PaperP1.Model.OneSidedPrimeCylinder
public import PaperP1.Model.RankChargedPrimeCylinder

/-! # Exponential moments and prime cylinders

Consolidated components retain their literal models, complete hypotheses and
original proof bodies, relocated into distinct model namespaces. The declaration
map records every original statement and source hash. No mathematical change.
-/

set_option autoImplicit false
@[expose] public noncomputable section

section ComponentExponentialDivergence

/-! # Actual exponential-moment divergence for multiplicative run starts
The literal independent prime-sign law and actual positive/total start
counts are explicit. The finite one-sided cylinder improvement is kept
separate from the original odd-prime asymptotic regime t>2.
Prime-sign foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0;
see docs/PAPER_C_REUSE.md. Four selected Challenge holes are deliberate.
-/

namespace PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence
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

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.count_eq (N L : ℕ) (ω : Sample) : runCount N L ω=
    PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.positiveCount_eq (N L : ℕ) (ω : Sample) : positiveCount N L ω=
    PaperP1.PositiveStarts.infiniteCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.positiveMGF_eq (N L : ℕ) (t : ℝ) : positiveMGF N L t=
    PaperP1.PositiveStarts.exponentialMoment (PaperP1.Model.dyadicBlock N) L t := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.totalMGF_eq (N L : ℕ) (t : ℝ) : totalMGF N L t=
    PaperP1.PrimeRunCylinder.totalExponentialMoment N L t := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.primeScale_eq (q : ℕ) : primeScale q=PaperP1.PrimeCylinderScale.size q := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.positiveRate_eq (t : ℝ) (q : ℕ) : positiveRate t q=
    PaperP1.PrimeCylinderDivergence.positiveRate t q := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.totalRate_eq (t : ℝ) (q : ℕ) : totalRate t q=
    PaperP1.PrimeCylinderDivergence.totalRate t q := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.oddPrimeFilter_eq : oddPrimeFilter=PaperP1.PrimeCylinderLiminf.oddPrimeIndices := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.cylinder_integrable (M : ℕ) (f : PaperP1.Model.SampleSpace M → ℝ) :
    Integrable (fun ω ↦ f (PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M ω))
      primeSignMeasure := by
  change Integrable (f ∘ PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M)
    PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure
  exact (PaperP1.Probability.integrable_finite_function
    (PaperP1.Model.InfiniteRademacher.infiniteRademacherMeasure.map
      (PaperP1.Probability.InfiniteCylinderTransfer.restrictToFinite M)) f).comp_measurable
        (PaperP1.Probability.CylinderExpectations.measurable_restrictToFinite M)

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.positive_integrable (N L : ℕ) (t : ℝ) :
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

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.total_integrable (N L : ℕ) (t : ℝ) :
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

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence.nominalMean_one (q : ℕ) : nominalMean (primeScale q) (q-1)=1 := by
  simp only [nominalMean, primeScale, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))

/-- Explicit integrability and a sharper finite lower bound under the actual law. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.exponential_divergence_finite_cylinder_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
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
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.exponential_divergence_prime_threshold_bounds (t : ℝ) (ht : 2<t) :
    0<(t-2)*Real.log 2 ∧ ∀ ε : ℝ, 0<ε → ∃ q₀ : ℕ, 3≤q₀ ∧
      ∀ q : ℕ, q₀≤q → Nat.Prime q →
        (t-2)*Real.log 2-ε≤positiveRate t q ∧
        (t-2)*Real.log 2-ε≤totalRate t q := by
  exact PaperP1.PrimeCylinderDivergence.companion_T19_7 t ht

/-- Literal extended-real lower limits along a nontrivial odd-prime filter. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.exponential_divergence_odd_prime_liminf (t : ℝ) (ht : 2<t) :
    Filter.NeBot oddPrimeFilter ∧ (0 : EReal)<((t-2)*Real.log 2 : ℝ) ∧
      (((t-2)*Real.log 2 : ℝ) : EReal)≤
        Filter.liminf (fun q ↦ (positiveRate t q : EReal)) oddPrimeFilter ∧
      (((t-2)*Real.log 2 : ℝ) : EReal)≤
        Filter.liminf (fun q ↦ (totalRate t q : EReal)) oddPrimeFilter := by
  exact ⟨PaperP1.PrimeCylinderLiminf.oddPrimeIndices_neBot,
    PaperP1.PrimeCylinderLiminf.companion_T19_7_liminf t ht⟩

/-- Both logarithms and both actual moments diverge, at nominal mean exactly one. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.exponential_divergence_logarithms_and_moments_diverge (t : ℝ) (ht : 2<t) (K : ℝ) :
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
end PaperP1Registry.RegistrationModels.ExponentialCylinders.ExponentialDivergence

end ComponentExponentialDivergence

section ComponentPrimeCylinders

/-! # Finite valuation cylinders and their actual affine forcing cost
The independent prime-sign law, actual counts, complete retained set and
finite forcing map are explicit Mathlib-only definitions. Four selected
statements cover finite layers, uniform density, exact forcing mass and
rank-charged actual moments, and the five-start factor-two example.
Prime-sign foundations are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0;
see docs/PAPER_C_REUSE.md. Four selected Challenge holes are deliberate.
-/

namespace PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders
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

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.positiveMGF_eq (N L : ℕ) (t : ℝ) : positiveMGF N L t=
    PaperP1.PositiveStarts.exponentialMoment (PaperP1.Model.dyadicBlock N) L t := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.totalMGF_eq (N L : ℕ) (t : ℝ) : totalMGF N L t=
    PaperP1.PrimeRunCylinder.totalExponentialMoment N L t := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.retainedParameters_eq (N q : ℕ) : retainedParameters N q=
    PaperP1.ValuationPrimeCylinder.retainedParameters N q := by
  ext u
  simp only [retainedParameters,PaperP1.ValuationPrimeCylinder.retainedParameters,
    PaperP1.PrimeRunStarts.parameters,mem_filter]
  rw [PaperP1.ValuationPrimeCylinder.parity_condition_iff_even]

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.retainedStarts_eq (N q : ℕ) : retainedStarts N q=PaperP1.ValuationPrimeCylinder.starts N q := by
  unfold retainedStarts PaperP1.ValuationPrimeCylinder.starts
  rw [retainedParameters_eq]

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.retainedCount_eq (N q : ℕ) : retainedCount N q=(PaperP1.ValuationPrimeCylinder.starts N q).card := by
  rw [retainedCount,retainedStarts_eq]

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.forcingSystem_eq (M : ℕ) (G : Finset ℕ) (L : ℕ) :
    forcingSystem M G L=PaperP1.RankChargedPrimeCylinder.system M G L := by
  apply LinearMap.ext
  intro σ
  funext i
  obtain ⟨x,i⟩ := i
  cases i <;> rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.forcingRhs_eq (G : Finset ℕ) (L : ℕ) :
    forcingRhs G L=PaperP1.RankChargedPrimeCylinder.rhs G L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.forcingRank_eq (N q : ℕ) : forcingRank N q=PaperP1.RankChargedPrimeCylinder.retainedRank N q := by
  change PaperP1.RankChargedPrimeCylinder.rank (cutoff N q) (retainedStarts N q) (q-1)=_
  rw [retainedStarts_eq]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders.forcingMass_eq (N q : ℕ) : forcingMass N q=
    PaperP1.Affine.uniformSolutionMass
      (PaperP1.RankChargedPrimeCylinder.system (PaperP1.SupportedPrimeCylinder.cutoff N q)
        (PaperP1.ValuationPrimeCylinder.starts N q) (q-1))
      (PaperP1.RankChargedPrimeCylinder.rhs (PaperP1.ValuationPrimeCylinder.starts N q) (q-1)) := by
  unfold forcingMass
  rw [forcingSystem_eq,forcingRhs_eq,retainedStarts_eq,
    PaperP1.Affine.uniformSolutionMass_eq_card_ratio]
  simp only [Fintype.card_eq_nat_card]
  rfl

/-- Explicit finite-layer count and both actual full moment bounds. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.prime_cylinders_finite_valuation_cylinders {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (k : ℕ) (t : ℝ) (ht : 0≤t) :
    layerBudget N q k≤(retainedCount N q : ℝ) ∧
    Real.exp (t*layerBudget N q k-(Nat.primeCounting (cutoff N q) : ℝ)*Real.log 2)≤
      positiveMGF N (q-1) t ∧
    Real.exp (t*layerBudget N q k-(Nat.primeCounting (cutoff N q) : ℝ)*Real.log 2)≤
      totalMGF N (q-1) t := by
  refine ⟨?_,?_,?_⟩
  · simpa only [layerBudget,retainedCount_eq] using
      PaperP1.ValuationLayerCounts.finite_geometric_lower hq.two_le hqN k
  · simpa only [positiveMGF_eq,layerBudget,PaperP1.ValuationLayerCounts.budget,
      cutoff,PaperP1.SupportedPrimeCylinder.cutoff,
      PaperP1.LocalRigidityCode.primeCount_eq_primeCounting] using
        PaperP1.ValuationLayerCounts.positive_exponential_lower hq hqN k t ht
  · simpa only [totalMGF_eq,layerBudget,PaperP1.ValuationLayerCounts.budget,
      cutoff,PaperP1.SupportedPrimeCylinder.cutoff,
      PaperP1.LocalRigidityCode.primeCount_eq_primeCounting] using
        PaperP1.ValuationLayerCounts.total_exponential_lower hq hqN k t ht

/-- Complete finite cover, fixed-prime density and a threshold independent of the prime. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.prime_cylinders_effective_retained_density :
    (∀ N q : ℕ, Nat.Prime q → q≤N →
      ((N : ℝ)-1)/((q : ℝ)+1)-3*(depth N q : ℝ)≤(retainedCount N q : ℝ) ∧
      (retainedCount N q : ℝ)≤(N : ℝ)/((q : ℝ)+1)+2*(depth N q : ℝ)) ∧
    (∀ q : ℕ, Nat.Prime q → Filter.Tendsto
      (fun N : ℕ ↦ (retainedCount N q : ℝ)/(N : ℝ)) Filter.atTop (nhds (1/((q : ℝ)+1)))) ∧
    ∀ ε : ℝ, 0<ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N → ∀ q : ℕ, Nat.Prime q → q≤N →
      |(retainedCount N q : ℝ)/(N : ℝ)-1/((q : ℝ)+1)|≤ε := by
  refine ⟨?_,?_,?_⟩
  · intro N q hq hqN
    simpa only [retainedCount_eq,depth,PaperP1.ValuationDensityBounds.depth] using
      PaperP1.ValuationDensityBounds.effective_count_bounds hq hqN
  · intro q hq
    simpa only [retainedCount_eq] using PaperP1.ValuationDensityBounds.retained_start_density hq
  · intro ε hε
    simpa only [retainedCount_eq] using PaperP1.ValuationDensityBounds.uniform_density_approximation ε hε

/-- Exact actual forcing probability, effective rank and both full-model moment bounds. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.prime_cylinders_rank_charged_moments {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    forcingMass N q=(2^forcingRank N q : ℝ)⁻¹ ∧
    forcingRank N q≤Nat.primeCounting (cutoff N q) ∧
    Real.exp (t*(retainedCount N q : ℝ)-(forcingRank N q : ℝ)*Real.log 2)≤positiveMGF N (q-1) t ∧
    Real.exp (t*(retainedCount N q : ℝ)-(forcingRank N q : ℝ)*Real.log 2)≤totalMGF N (q-1) t := by
  rw [forcingMass_eq,forcingRank_eq,retainedCount_eq,positiveMGF_eq,totalMGF_eq]
  refine ⟨PaperP1.RankChargedPrimeCylinder.retained_forcing_mass hq hqN,?_,
    PaperP1.RankChargedPrimeCylinder.positive_exponential_card_lower hq hqN t ht,
    PaperP1.RankChargedPrimeCylinder.total_exponential_card_lower hq hqN t ht⟩
  simpa only [cutoff,PaperP1.SupportedPrimeCylinder.cutoff,
    PaperP1.LocalRigidityCode.primeCount_eq_primeCounting] using
      PaperP1.RankChargedPrimeCylinder.retained_rank_le_primeCount N q

/-- A nonempty exact finite example with at least a factor-two probability gain. -/
theorem _root_.PaperP1Registry.Registration.ExponentialCylinders.prime_cylinders_five_start_gain :
    retainedCount 18 3=5 ∧ forcingRank 18 3≤10 ∧ Nat.primeCounting 36=11 ∧
    ∀ t : ℝ, 0≤t →
      Real.exp (5*t-10*Real.log 2)≤positiveMGF 18 2 t ∧
      Real.exp (5*t-10*Real.log 2)≤totalMGF 18 2 t := by
  refine ⟨?_,?_,?_,fun t ht ↦ ?_⟩
  · simpa only [retainedCount_eq] using PaperP1.RankChargedPrimeCylinder.retained_start_count_example
  · simpa only [forcingRank_eq] using PaperP1.RankChargedPrimeCylinder.retained_rank_example
  · simpa only [PaperP1.LocalRigidityCode.primeCount_eq_primeCounting,
      PaperP1.SupportedPrimeCylinder.cutoff] using PaperP1.RankChargedPrimeCylinder.prime_count_example
  · exact ⟨PaperP1.RankChargedPrimeCylinder.positive_explicit_example t ht,
      PaperP1.RankChargedPrimeCylinder.total_explicit_example t ht⟩
end PaperP1Registry.RegistrationModels.ExponentialCylinders.PrimeCylinders

end ComponentPrimeCylinders
