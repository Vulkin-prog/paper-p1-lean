module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Tactic.NormNum
public import PaperP1.Analysis.UnconditionalPrintedAnchorObstruction
public import PaperP1.Asymptotics.ActualPairPhase
public import PaperP1.Asymptotics.MomentObstructionSequence
public import PaperP1.Asymptotics.OptimalThirdCumulant
public import PaperP1.Model.FourthRunFactorialCumulant
public import PaperP1.Model.RetainedMomentTransfer

/-! # Factorial cumulants, moments and private obstructions

Consolidated components retain their literal models, complete hypotheses and
original proof bodies, relocated into distinct model namespaces. The declaration
map records every original statement and source hash. No mathematical change.
-/

set_option autoImplicit false
@[expose] public noncomputable section

section ComponentFactorialCumulants

/-! # Actual factorial cumulants of multiplicative-run counts
The literal independent prime-sign model, full counts, falling-factorial
moments and heterogeneous centered coefficients are explicit. The exact
second-cumulant moving coefficient and optimal positive third-cumulant power
are stated with their original parameter order. Selected model foundations
are adapted through P1 from Paper C, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
The five selected Challenge theorem holes are deliberate statement placeholders.
-/

namespace PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants
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

/-- Actual moments under the prime-sign law. -/
def moment (N L j : ℕ) : ℝ := ∫ ω, (runCount N L ω : ℝ)^j ∂primeSignMeasure

def actualMean (N L : ℕ) : ℝ := moment N L 1

/-- The second factorial cumulant, with every actual marginal retained. -/
def secondCumulant (N L : ℕ) : ℝ := moment N L 2-actualMean N L-(actualMean N L)^2

/-- Actual singleton probabilities of the complete count law. -/
def sourceMass (N L k : ℕ) : ℝ := primeSignMeasure.real {ω | runCount N L ω=k}

def nominalMean (N L : ℕ) : ℝ := (N : ℝ)*(2^L : ℝ)⁻¹

/-- Actual real-valued indicator of a start, of either sign. -/
def indicator (x L : ℕ) (ω : Sample) : ℝ := if startIndicator x L ω then 1 else 0

/-- Actual heterogeneous one-window probability. -/
def marginal (x L : ℕ) : ℝ := ∫ ω, indicator x L ω ∂primeSignMeasure

/-- Actual joint start mass, including incompatible families. -/
def jointMoment (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, indicator x L ω ∂primeSignMeasure

/-- Actual centered joint coefficient, using every window's own mean. -/
def centeredCoefficient (L : ℕ) (A : Finset ℕ) : ℝ :=
  ∫ ω, ∏ x ∈ A, (indicator x L ω-marginal x L) ∂primeSignMeasure

/-- Actual falling-factorial moment of the complete count. -/
def factorialMoment (N L r : ℕ) : ℝ :=
  ∫ ω, ((runCount N L ω).descFactorial r : ℝ) ∂primeSignMeasure

/-- Third factorial cumulant of the literal count law. -/
def thirdCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 3-3*factorialMoment N L 2*factorialMoment N L 1+2*(factorialMoment N L 1)^3

/-- Fourth factorial cumulant of the literal count law. -/
def fourthCumulant (N L : ℕ) : ℝ :=
  factorialMoment N L 4-4*factorialMoment N L 3*factorialMoment N L 1-
    3*(factorialMoment N L 2)^2+12*factorialMoment N L 2*(factorialMoment N L 1)^2-
    6*(factorialMoment N L 1)^4

/-- The literal moving residue-dependent scale of the second cumulant. -/
def principalSecondScale (N L : ℕ) : ℝ :=
  (((L%3 : ℕ) : ℝ)+2)/(18*(2 : ℝ)^(((L%3 : ℕ) : ℝ)/3))*
    (nominalMean N L)^(5/3 : ℝ)*L*(N : ℝ)^(-2/3 : ℝ)

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.runCount_eq (N L : ℕ) (ω : Sample) :
    runCount N L ω=PaperP1.Model.InfiniteStarts.infiniteStartCount (PaperP1.Model.dyadicBlock N) L ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.factorialMoment_eq (N L r : ℕ) :
    factorialMoment N L r=PaperP1.FactorialCountMoments.factorialCountMoment (PaperP1.Model.dyadicBlock N) L r := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.marginal_eq (x L : ℕ) : marginal x L=PaperP1.Model.InfiniteStarts.infiniteMarginal x L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.jointMoment_eq (L : ℕ) (A : Finset ℕ) :
    jointMoment L A=PaperP1.Model.InfiniteStarts.infiniteJointMoment L A := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.centeredCoefficient_eq (L : ℕ) (A : Finset ℕ) :
    centeredCoefficient L A=PaperP1.Model.InfiniteStarts.infiniteCenteredCoefficient L A := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.third_eq (N L : ℕ) : thirdCumulant N L=
    PaperP1.ThirdRunFactorialCumulant.thirdFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.fourth_eq (N L : ℕ) : fourthCumulant N L=
    PaperP1.FourthRunFactorialCumulant.fourthFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.second_eq (N L : ℕ) : secondCumulant N L=
    PaperP1.RegularCumulantTransfer.secondFactorialCumulant (PaperP1.Model.dyadicBlock N) L := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants.principalScale_eq (N L : ℕ) : principalSecondScale N L=
    PaperP1.ChannelMassPhaseEquivalent.phaseMass N L 3 := by
  exact (PaperP1.PrincipalPairPhaseComparison.phase_three N L).symm

/-- All falling-factorial observables are genuinely integrable, and their
subset expansion uses the actual joint probabilities of the original starts. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_factorial_source (N L r : ℕ) :
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

/-- Exact third-cumulant identity, including every heterogeneous marginal
and repeated-index correction, at all finite scales. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_third_exact_identity (N L : ℕ) :
    thirdCumulant N L=
      6*(∑ A ∈ (Ico N (2*N)).powersetCard 3, centeredCoefficient L A)-
      6*(∑ e ∈ (Ico N (2*N)).powersetCard 2,
        (∑ x ∈ e, marginal x L)*centeredCoefficient L e)+
      2*∑ x ∈ Ico N (2*N), (marginal x L)^3 :=
by
  simpa only [third_eq,centeredCoefficient_eq,marginal_eq,PaperP1.Model.dyadicBlock] using
    (PaperP1.ThirdRunFactorialCumulant.exact_formula
      (N:=N) (L:=L) (G:=PaperP1.Model.dyadicBlock N) Subset.rfl)

/-- Exact fourth-cumulant identity with the complete pair-square, triple,
heterogeneous pair and diagonal terms. No common marginal is substituted. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_fourth_exact_identity (N L : ℕ) :
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

/-- Full critical-band equivalent of the actual second factorial cumulant,
with the exact moving residue coefficient and nominal mean. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_principal_second_equivalent (C τ : ℝ) (hτ : 0 < τ) :
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

/-- The optimal positive 41/30 power for the actual third factorial cumulant.
The positive lower constant depends only on C, before the upper margin. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_optimal_third_cumulant (C : ℝ) :
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

end PaperP1Registry.RegistrationModels.CumulantsObstructions.FactorialCumulants

end ComponentFactorialCumulants

section ComponentMomentObstruction

/-! # Fixed-order moments do not imply a polynomial approximation rate
The actual probability masses, finite perturbation, all moment sums and
half-l1 distance are literal Mathlib expressions. The a=2 endpoint is retained
for positivity and excluded from the unique-changed-moment assertion. These
are constructed probability models, not the multiplicative-run count law.
Only the five selected Challenge theorem holes are deliberate placeholders.
-/

namespace PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction
open Finset
open scoped Classical

/-- Unit-mean Poisson singleton masses. -/
def poissonMass (k : ℕ) : ℝ := Real.exp (-1)*(1 : ℝ)^k/(k.factorial : ℝ)

def shift (f : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | k+1 => f k

/-- The literal quadratic Poisson reference at mean one. -/
def qMass (a : ℝ) (k : ℕ) : ℝ :=
  poissonMass k+(a/2)*(shift (shift poissonMass) k-2*shift poissonMass k+poissonMass k)

/-- Finite-difference coefficients; choose(m,k) vanishes when k>m. -/
def differenceCoefficient (m k : ℕ) : ℝ := (-1 : ℝ)^(m-k)*(m.choose k : ℝ)

def epsilon (m : ℕ) (a : ℝ) : ℝ :=
  (1-a/2)*Real.exp (-1)/(2*(m.factorial : ℝ))

/-- The actual finite perturbation of the quadratic reference. -/
def pMass (m : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  qMass a k+epsilon m a*differenceCoefficient m k

/-- Half of singleton l1 distance; summability is asserted explicitly below. -/
def totalVariation (m : ℕ) (a : ℝ) : ℝ :=
  (∑' k : ℕ, |pMass m a k-qMass a k|)/2

/-- The moving moment order in the actual obstruction sequence. -/
def order (N : ℕ) : ℕ := ⌊Real.sqrt (Real.log (N : ℝ))⌋₊

def parameter (N : ℕ) : ℝ := Real.log (N : ℝ)*(N : ℝ)^(-(2/3 : ℝ))

def Valid (N : ℕ) : Prop := 3 ≤ order N ∧ 0 ≤ parameter N ∧ parameter N ≤ 1

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.qMass_eq (a : ℝ) (k : ℕ) : qMass a k=PaperP1.MomentObstructionMass.qMass a k := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.qMass_fun_eq (a : ℝ) : qMass a=PaperP1.MomentObstructionMass.qMass a := funext (qMass_eq a)

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.coefficient_eq (m k : ℕ) : differenceCoefficient m k=
    ((PaperP1.Probability.forwardDifference : PaperP1.Probability.SignedLaw ℝ)^m).coeff k :=
  (PaperP1.DifferenceCoefficients.forwardDifference_pow_coeff m k).symm

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.epsilon_eq (m : ℕ) (a : ℝ) : epsilon m a=PaperP1.MomentObstructionMass.epsilon m a := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.pMass_eq (m : ℕ) (a : ℝ) (k : ℕ) : pMass m a k=PaperP1.MomentObstructionMass.pMass m a k := by
  simp only [pMass,qMass_eq,epsilon_eq,coefficient_eq,PaperP1.MomentObstructionMass.pMass]

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.pMass_fun_eq (m : ℕ) (a : ℝ) : pMass m a=PaperP1.MomentObstructionMass.pMass m a := funext (pMass_eq m a)

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.totalVariation_eq (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    totalVariation m a=PaperP1.MomentObstructionLog.distance m a := by
  have h := PaperP1.MomentObstruction.totalVariation_exact m (by omega) hm a ha0 ha2
  simp only [PaperP1.AtomicProbability.totalVariation,
    PaperP1.MomentObstructionMass.pLaw_real_singleton,
    PaperP1.MomentObstructionMass.qLaw_real_singleton] at h
  simpa only [totalVariation,pMass_eq,qMass_eq,PaperP1.MomentObstructionLog.distance] using h

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.order_eq (N : ℕ) : order N=PaperP1.MomentObstructionSequence.order N := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.parameter_eq (N : ℕ) : parameter N=PaperP1.MomentObstructionSequence.parameter N := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction.valid_eq (N : ℕ) : Valid N ↔ PaperP1.MomentObstructionSequence.Valid N := by rfl

/-- Genuine probability masses with a uniform pointwise comparison.
The construction remains nonnegative throughout the full interval [0,2]. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_normalized_probabilities (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    HasSum (qMass a) 1 ∧ HasSum (pMass m a) 1 ∧
    ∀ k : ℕ, 0 ≤ qMass a k ∧ 0 ≤ pMass m a k ∧
      qMass a k/2 ≤ pMass m a k ∧ pMass m a k ≤ 3/2*qMass a k :=
by
  refine ⟨?_,?_,?_⟩
  · simpa only [qMass_fun_eq] using PaperP1.MomentObstructionMass.hasSum_qMass a
  · simpa only [pMass_fun_eq] using PaperP1.MomentObstructionMass.hasSum_pMass m hm a
  · intro k
    simpa only [qMass_eq,pMass_eq] using And.intro
      (PaperP1.MomentObstructionMass.qMass_nonneg a ha0 ha2 k)
      (And.intro (PaperP1.MomentObstructionMass.pMass_nonneg m a ha0 ha2 k)
        (PaperP1.MomentObstructionMass.pMass_pointwise_bounds m a ha0 ha2 k))

/-- Every factorial moment exists as an unconditionally convergent mass sum.
In the original range [0,1], exactly order m changes, including among higher
orders; at a=2 the perturbation vanishes and that iff is not asserted. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_all_factorial_series (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    HasSum (qMass a) 1 ∧ HasSum (pMass m a) 1 ∧
    (∀ k : ℕ, 0 ≤ qMass a k ∧ 0 ≤ pMass m a k) ∧
    ∀ j : ℕ,
      HasSum (fun k : ℕ ↦ qMass a k*(k.descFactorial j : ℝ)) (1+a*(j.choose 2 : ℝ)) ∧
      HasSum (fun k : ℕ ↦ pMass m a k*(k.descFactorial j : ℝ))
        (1+a*(j.choose 2 : ℝ)+(if j=m then (1-a/2)*Real.exp (-1)/2 else 0)) ∧
      ((∑' k : ℕ, pMass m a k*(k.descFactorial j : ℝ))=
        (∑' k : ℕ, qMass a k*(k.descFactorial j : ℝ)) ↔ j ≠ m) :=
by
  obtain ⟨hQn,hPn,hpos⟩ := _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_normalized_probabilities m (by omega) a ha0 (by linarith)
  refine ⟨hQn,hPn,(fun k ↦ ⟨(hpos k).1,(hpos k).2.1⟩),?_⟩
  intro j
  have hQ : HasSum (fun k : ℕ ↦ qMass a k*(k.descFactorial j : ℝ))
      (1+a*(j.choose 2 : ℝ)) := by
    exact PaperP1.PoissonFactorialMoments.hasSum_quadratic_one_factorial a j
  have hQS := PaperP1.PoissonFactorialMoments.hasSum_quadratic_one_factorial a j
  have hP := PaperP1.MomentObstructionMoments.hasSum_pMass_weighted m a
    (fun k : ℕ ↦ (k.descFactorial j : ℝ)) hQS
  have hc : PaperP1.MomentObstructionMass.epsilon m a*
      (if m=j then (m.factorial : ℝ) else 0)=
      (if j=m then (1-a/2)*Real.exp (-1)/2 else 0) := by
    by_cases hj : j=m
    · subst j
      simp only [ite_true]
      exact PaperP1.MomentObstructionMass.epsilon_mul_factorial m a
    · rw [ite_eq_right (Ne.symm hj),mul_zero,ite_eq_right hj]
  have hPP : HasSum (fun k : ℕ ↦ pMass m a k*(k.descFactorial j : ℝ))
      (1+a*(j.choose 2 : ℝ)+(if j=m then (1-a/2)*Real.exp (-1)/2 else 0)) := by
    simpa only [pMass_eq,PaperP1.DifferenceCoefficients.difference_factorial_moment,hc] using hP
  refine ⟨hQ,hPP,?_⟩
  rw [hPP.tsum_eq,hQ.tsum_eq]
  constructor
  · intro heq hj
    rw [hj,ite_eq_left rfl] at heq
    have hh : 0 < 1-a/2 := by linarith
    have hp : 0 < (1-a/2)*Real.exp (-1)/2 := by positivity
    linarith
  · intro hj
    rw [ite_eq_right hj,add_zero]

/-- Exact positive total variation and the original uniform exponential-moment
bound, with absolute distance and exponential-series summability explicit. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_distance_and_exponential (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Summable (fun k : ℕ ↦ |pMass m a k-qMass a k|) ∧
    totalVariation m a=(1-a/2)*(2 : ℝ)^(m-2)/(Real.exp 1*(m.factorial : ℝ)) ∧
    ∀ t : ℝ, Summable (fun k : ℕ ↦ pMass m a k*Real.exp (t*k)) ∧
      (∑' k : ℕ, pMass m a k*Real.exp (t*k)) ≤
        3/2*Real.exp (Real.exp t-1)*(1+(1/2)*(Real.exp t-1)^2) :=
by
  obtain ⟨hQ,hP,_⟩ := _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_normalized_probabilities m (by omega) a ha0 (by linarith)
  refine ⟨(hP.summable.sub hQ.summable).abs,?_,?_⟩
  · exact totalVariation_eq m (by omega) a ha0 (by linarith)
  · intro t
    have hs := (PaperP1.MomentObstructionMoments.hasSum_pMass_weighted m a
      (fun k : ℕ ↦ Real.exp (t*k))
      (PaperP1.MomentObstructionMoments.hasSum_qMass_exp a t)).summable
    have hb := PaperP1.MomentObstruction.exponential_moment_le m (by omega) a ha0 (by linarith) t 1 ha1
    change (∫ k : ℕ, Real.exp (t*k) ∂(PaperP1.AtomicProbability.ofMass _ _ _ : MeasureTheory.Measure ℕ)) ≤ _ at hb
    rw [PaperP1.AtomicProbability.ofMass_integral] at hb
    exact ⟨by simpa only [pMass_eq] using hs,by simpa only [pMass_eq] using hb⟩

/-- At every fixed factorial order the actual moving perturbation eventually
has exactly the reference moment; its normalized nonnegative masses are part
of the conclusion, rather than assumed. This is a constructed obstruction
family, not an identification with the multiplicative-run count law. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_fixed_order_matching (r : ℕ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, Valid N ∧
      HasSum (pMass (order N) (parameter N)) 1 ∧ HasSum (qMass (parameter N)) 1 ∧
      (∀ k : ℕ, 0 ≤ qMass (parameter N) k ∧ 0 ≤ pMass (order N) (parameter N) k) ∧
      HasSum (fun k : ℕ ↦ pMass (order N) (parameter N) k*(k.descFactorial r : ℝ))
        (1+parameter N*(r.choose 2 : ℝ)) ∧
      HasSum (fun k : ℕ ↦ qMass (parameter N) k*(k.descFactorial r : ℝ))
        (1+parameter N*(r.choose 2 : ℝ)) :=
by
  obtain ⟨N₀,h⟩ := Filter.eventually_atTop.mp
    (PaperP1.MomentObstructionSequence.valid_eventually.and
      (PaperP1.MomentObstructionSequence.order_tendsto.eventually (Filter.eventually_gt_atTop r)))
  refine ⟨max 2 N₀,by omega,?_⟩
  intro N hN
  obtain ⟨hV,hr⟩ := h N (by omega)
  have hv : Valid N := (valid_eq N).mpr hV
  have hne : r ≠ order N := by exact Nat.ne_of_lt hr
  obtain ⟨hqn,hpn,hpos,hseries⟩ := _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_all_factorial_series (order N) hv.1 (parameter N) hv.2.1 hv.2.2
  obtain ⟨hq,hp,_hiff⟩ := hseries r
  exact ⟨hv,hpn,hqn,hpos,by simpa only [ite_eq_right hne,add_zero] using hp,hq⟩

/-- The genuine probability-model distance exceeds every fixed polynomial
rate. Its explicit logarithmic error is uniform over all a in [0,1]. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_uniform_subpolynomial (γ : ℝ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, 3 ≤ order N ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (N : ℝ)^(-γ) < totalVariation (order N) a ∧
        |Real.log (totalVariation (order N) a)+
          (1/2)*Real.sqrt (Real.log N)*Real.log (Real.log N)| ≤ 3*Real.sqrt (Real.log N) :=
by
  obtain ⟨NT,hT⟩ := PaperP1.MomentObstructionSequence.uniform_distance_exceeds_power γ hγ
  obtain ⟨NG,hG⟩ := Filter.eventually_atTop.mp
    (PaperP1.MomentObstructionSequence.valid_eventually.and
      (PaperP1.MomentObstructionSequence.log_nat_tendsto.eventually (Filter.eventually_ge_atTop 9)))
  refine ⟨max 2 (max NT NG),by omega,?_⟩
  intro N hN
  obtain ⟨hv,hl⟩ := hG N (by omega)
  have hM : 3 ≤ order N := hv.1
  refine ⟨hM,?_⟩
  intro a ha0 ha1
  rw [totalVariation_eq (order N) (by omega) a ha0 (by linarith)]
  exact ⟨hT N (by omega) a ha0 ha1,
    PaperP1.MomentObstructionLog.log_distance_sqrt_log_bound N hl a ha0 ha1⟩

end PaperP1Registry.RegistrationModels.CumulantsObstructions.MomentObstruction

end ComponentMomentObstruction

section ComponentPrivateObstruction

/-! # Actual arithmetic private forcing and universal anchor obstructions
The independent finite prime signs, retained population, arithmetic pivots,
actual forcing and every offsite cost are explicit Mathlib definitions.
The two T19.17 coefficients and the arbitrary independent auxiliary law are
preserved. Selected model foundations are adapted through P1 from Paper C,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0; see docs/PAPER_C_REUSE.md.
Only the four selected Challenge theorem holes are deliberate placeholders.
-/

namespace PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction
open Finset MeasureTheory
open scoped Classical
abbrev F₂ := ZMod 2
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Prime coordinates up to the inclusive cutoff M. -/
def PrimeUpTo (M : ℕ) := {p : Fin (M+1) // Nat.Prime p.val}
instance primeFintype (M : ℕ) : Fintype (PrimeUpTo M) := Subtype.fintype _
instance primeDecidableEq (M : ℕ) : DecidableEq (PrimeUpTo M) := Classical.decEq _
abbrev Sample (M : ℕ) := PrimeUpTo M → F₂

def parity (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)

def value {M : ℕ} (ω : Sample M) (n : ℕ) : F₂ :=
  ∑ p : PrimeUpTo M, ω p * parity n p.val.val

def rawWord {M K : ℕ} (j : ℕ) (ω : Sample M) : Fin (K+1) → F₂ :=
  fun i ↦ value ω (j+i.val)

/-- The largest prime with odd valuation, including the prime 2; 1 for squares. -/
def largestOddPrime (n : ℕ) : ℕ :=
  max 1 ((n.factorization.mapRange (fun e : ℕ ↦ e%2) (by simp)).support.sup id)

def boundaryBlock (N : ℕ) : Finset ℕ := (Ico N (2*N)).image (fun x ↦ x-1)
def smallVertices (j B Y : ℕ) : Finset (Fin B) :=
  univ.filter fun i ↦ largestOddPrime (j+i.val) ≤ Y

/-- At most one small pivot in the entire maximal support. -/
def retained (N B Y : ℕ) : Finset ℕ :=
  (boundaryBlock N).filter fun j ↦ (smallVertices j B Y).card ≤ 1

def badAt (N B Z : ℕ) (i : Fin B) : Finset ℕ :=
  (Ico N (2*N)).filter fun x ↦ largestOddPrime (x-1+i.val) ≤ Z

def fullGood (N B Z : ℕ) : Finset ℕ :=
  boundaryBlock N \ ((univ.biUnion (badAt N B Z)).image (fun x ↦ x-1))

def cutoff (N : ℕ) : ℕ := ⌊(Real.log (N : ℝ))^5⌋₊
abbrev Free {K : ℕ} (anchor : Fin (K+1)) := {i : Fin (K+1) // i ≠ anchor}

/-- Pure arithmetic admissibility, before sampling any signs. -/
structure WindowData (M j K Y : ℕ) (anchor : Fin (K+1)) : Prop where
  boundary_pos : 0 < j
  support_cutoff : j+(K+1) ≤ M+1
  small_pos : 1 ≤ Y
  word_width : K+1 ≤ Y
  good : ∀ i : Free anchor, Y < largestOddPrime (j+i.val.val)

structure PrivateData (M Y K : ℕ) (G : Finset ℕ) (anchor : G → Fin (K+1)) : Prop where
  window : ∀ j : G, WindowData M j.val K Y (anchor j)

structure HybridData (M Y K : ℕ) (G Good : Finset ℕ) (anchor : G → Fin (K+1)) : Prop where
  anchored : PrivateData M Y K G anchor
  good : ∀ j : G, j.val ∈ Good → ∀ i : Fin (K+1), Y < largestOddPrime (j.val+i.val)

/-- Uniform independent prime signs, expressed as a finite normalized sum. -/
def average {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  ∑ ω, (Fintype.card Ω : ℝ)⁻¹*f ω

def orbit {K : ℕ} (b u : Fin (K+1) → F₂) : Prop := ∃ s : F₂, u=fun i ↦ b i+s

def indicator {M K : ℕ} {G : Finset ℕ} (b : Fin (K+1) → F₂) (j : G) (ω : Sample M) : Bool :=
  decide (orbit b (rawWord j.val ω))

def indicatorValue (b : Bool) : ℝ := if b then 1 else 0

/-- Only the actual nonanchor private primes are modified. -/
def force {M K : ℕ} {G : Finset ℕ} (anchor : G → Fin (K+1))
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M) (b : Fin (K+1) → F₂)
    (j : G) (ω : Sample M) : Sample M :=
  ω + ∑ i : Free (anchor j),
    (b i.val-b (anchor j)-value ω ((j.val+i.val.val)*(j.val+(anchor j).val))) • Pi.single (q j i) 1

def offsite {M K : ℕ} {G : Finset ℕ} (anchor : G → Fin (K+1))
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M) (b : Fin (K+1) → F₂) : ℝ :=
  ∑ j : G, average (fun ω : Sample M ↦ indicatorValue (indicator b j ω)) *
    average (fun ω : Sample M ↦ ∑ k ∈ (univ : Finset G).erase j,
      |indicatorValue (indicator b k ω)-indicatorValue (indicator b k (force anchor q b j ω))|)

/-- The exact printed lower scale, including the offset coefficient. -/
def nominal (N L i : ℕ) (a : ℝ) : ℝ :=
  (2^(2*i) : ℝ)⁻¹*((N : ℝ)*(2^L : ℝ)⁻¹)^2*(N : ℝ)^(-a)

def randomizedOffsite {M K : ℕ} {G : Finset ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (b : Fin (K+1) → F₂) (F : G → Sample M → Ξ → Sample M) : ℝ :=
  ∑ j : G, (2^K : ℝ)⁻¹*average (fun ω : Sample M ↦
    ∫ ξ, ∑ k ∈ (univ : Finset G).erase j,
      |indicatorValue (indicator b k ω)-indicatorValue (indicator b k (F j ω ξ))| ∂μ)

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.parity_eq (n : ℕ) : parity n = PaperP1.Arithmetic.parityVec n := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.value_eq {M : ℕ} (ω : Sample M) (n : ℕ) : value ω n = PaperP1.Model.valueBit ω n := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.rawWord_eq {M K : ℕ} (j : ℕ) (ω : Sample M) :
    rawWord (K:=K) j ω = PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K+1) ↦ j+i.val) ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.largest_eq (n : ℕ) : largestOddPrime n = PaperP1.OddPrimePivot.largestOddPrime n := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.retained_eq (N B Y : ℕ) : retained N B Y = PaperP1.AnchoredDyadicField.retainedBoundaries N B Y := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.good_eq (N B Z : ℕ) : fullGood N B Z = PaperP1.RandomizedDyadicHybridField.fullGood N B Z := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.toSource {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor) : PaperP1.AnchoredPrivateField.Data M Y K G anchor where
  window := fun j ↦ ⟨(A.window j).boundary_pos,(A.window j).support_cutoff,
    (A.window j).small_pos,(A.window j).word_width,(A.window j).good⟩

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.hybridToSource {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : HybridData M Y K G Good anchor) : PaperP1.RandomizedHybridField.Data M Y K G Good anchor where
  anchored := toSource A.anchored
  good := A.good

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.average_eq {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    average f = PaperP1.UniformFubini.average f := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.indicator_eq {M K : ℕ} {G : Finset ℕ} (b : Fin (K+1) → F₂) (j : G) (ω : Sample M) :
    indicator b j ω = PaperP1.AnchoredPrivateField.indicator b j ω := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.force_eq {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor)
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M)
    (hq : ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val))
    (b : Fin (K+1) → F₂) (j : G) (ω : Sample M) :
    force anchor q b j ω = PaperP1.AnchoredPrivateField.force (toSource A) b j ω := by
  have he : q j=PaperP1.AnchoredWindowForcing.pivots ((toSource A).window j) := by
    funext i
    apply Subtype.ext
    apply Fin.ext
    exact hq j i
  unfold force PaperP1.AnchoredPrivateField.force PaperP1.AnchoredWindowForcing.force
    PaperP1.AnchoredPrivateForcing.force PaperP1.PrivatePrimeForcing.forceWord
    PaperP1.PrivatePrimeForcing.liftBlock
  rw [he]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.offsite_eq {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor)
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M)
    (hq : ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val)) (b : Fin (K+1) → F₂) :
    offsite anchor q b = PaperP1.AnchoredPrivateField.offsite (toSource A) b := by
  simp only [offsite,indicator_eq,force_eq A q hq]
  rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.randomizedOffsite_eq {M K : ℕ} {G : Finset ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (b : Fin (K+1) → F₂) (F : G → Sample M → Ξ → Sample M) :
    randomizedOffsite μ b F = PaperP1.PrivateForcingMeasureObservation.offsite μ b F := by rfl

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.fromSource {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PaperP1.AnchoredPrivateField.Data M Y K G anchor) : PrivateData M Y K G anchor where
  window := fun j ↦ ⟨(A.window j).boundary_pos,(A.window j).cutoff,
    (A.window j).small_pos,(A.window j).word_width,(A.window j).good⟩

theorem _root_.PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction.hybridFromSource {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PaperP1.RandomizedHybridField.Data M Y K G Good anchor) : HybridData M Y K G Good anchor where
  anchored := fromSource A.anchored
  good := A.good

/-- The retained population admits anchors and actual private prime choices.
Every admissible arithmetic anchor rule gives such a field. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.private_obstruction_admissible_fields {N B Y K M : ℕ} (hN : 2 ≤ N) (hKB : K+1 ≤ B)
    (hBY : B ≤ Y) (hM : 2*N+B ≤ M) :
    (∃ anchor : retained N B Y → Fin (K+1), ∀ j i,
      largestOddPrime (j.val+i.val) ≤ Y → i=anchor j) ∧
    ∀ anchor : retained N B Y → Fin (K+1),
      (∀ j i, largestOddPrime (j.val+i.val) ≤ Y → i=anchor j) →
      PrivateData M Y K (retained N B Y) anchor ∧
      (∃ q : ∀ j : retained N B Y, Free (anchor j) → PrimeUpTo M,
        ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val)) ∧
      ∀ Z : ℕ, Y ≤ Z →
        HybridData M Y K (retained N B Y) (fullGood N B Z) anchor ∧
        ∃ q : ∀ j : retained N B Y, j.val ∈ fullGood N B Z → Fin (K+1) → PrimeUpTo M,
          ∀ j hj i, (q j hj i).val.val=largestOddPrime (j.val+i.val) :=
by
  constructor
  · exact PaperP1.AnchoredDyadicField.exists_anchor_rule hKB
  · intro anchor hrule
    have AS := PaperP1.AnchoredDyadicField.data hN hKB hBY hM anchor hrule
    refine ⟨fromSource AS,⟨(fun j ↦ PaperP1.AnchoredWindowForcing.pivots (AS.window j)),?_⟩,?_⟩
    · intro j i
      rfl
    · intro Z hYZ
      have HS := PaperP1.RandomizedDyadicHybridField.data hN hKB hBY hYZ hM anchor hrule
      refine ⟨hybridFromSource HS,PaperP1.RandomizedHybridField.fullPivots HS,?_⟩
      intro j hj i
      rfl

/-- Full sample conditional law for every observable, with the arithmetic
anchor and every small prime preserved, and exact source-word orientation. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.private_obstruction_conditional_forcing {M Y K : ℕ} {G : Finset ℕ} {anchor : G → Fin (K+1)}
    (A : PrivateData M Y K G anchor)
    (q : ∀ j : G, Free (anchor j) → PrimeUpTo M)
    (hq : ∀ j i, (q j i).val.val=largestOddPrime (j.val+i.val.val))
    (b : Fin (K+1) → F₂) (j : G) :
    (∀ f : Sample M → ℝ, average (fun ω ↦ f (force anchor q b j ω)) =
      average (fun ω ↦ if orbit b (rawWord j.val ω) then f ω else 0)/(2^K : ℝ)⁻¹) ∧
    ∀ ω : Sample M,
      value (force anchor q b j ω) (j.val+(anchor j).val)=value ω (j.val+(anchor j).val) ∧
      (∀ p : PrimeUpTo M, p.val.val ≤ Y → force anchor q b j ω p=ω p) ∧
      rawWord j.val (force anchor q b j ω)=
        fun i ↦ b i+(value ω (j.val+(anchor j).val)-b (anchor j)) :=
by
  have hforce := force_eq A q hq b j
  constructor
  · intro f
    simp only [hforce,average_eq]
    have hs := PaperP1.AnchoredWindowForcing.full_conditional ((toSource A).window j) b f
    simp only [Nat.add_sub_cancel] at hs
    refine hs.trans ?_
    congr 1
    apply PaperP1.UniformFubini.congr
    intro ω
    by_cases hp : orbit b (rawWord j.val ω)
    · have hex : ∃ s : F₂, PaperP1.PrivateValueSystem.valueSystem M
          (fun k : Fin (K+1) ↦ j.val+k.val) ω=(fun i ↦ b i+s) := hp
      rw [ite_eq_left hex,ite_eq_left hp]
    · have hex : ¬∃ s : F₂, PaperP1.PrivateValueSystem.valueSystem M
          (fun k : Fin (K+1) ↦ j.val+k.val) ω=(fun i ↦ b i+s) := hp
      rw [ite_eq_right hex,ite_eq_right hp]
  · intro ω
    simp only [hforce,value_eq]
    refine ⟨PaperP1.AnchoredWindowForcing.preserves_anchor ((toSource A).window j) b ω,?_,
      PaperP1.AnchoredWindowForcing.actual_orientation ((toSource A).window j) b ω⟩
    intro p hp
    exact congrFun (PaperP1.AnchoredWindowForcing.preserves_small ((toSource A).window j) b ω) ⟨p,hp⟩

/-- The complete deterministic printed T19.17 obstruction. One cutoff precedes
all maximal supports, both offsets, every arithmetic anchor and source word.
No census or analytic bound is assumed. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.private_obstruction_deterministic_obstruction (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1/10) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L+E+2 : ℕ) : ℝ) ≤ D*Real.log N → 2*N+(L+E+2) ≤ M →
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ anchor : retained N (L+E+2) (2*(L+E+2)) → Fin (L+i.val+1),
      ∀ _field : PrivateData M (2*(L+E+2)) (L+i.val)
        (retained N (L+E+2) (2*(L+E+2))) anchor,
      ∀ q : ∀ j : retained N (L+E+2) (2*(L+E+2)), Free (anchor j) → PrimeUpTo M,
      (∀ j k, (q j k).val.val=largestOddPrime (j.val+k.val.val)) →
      ∀ b : Fin (L+i.val+1) → F₂, (1-η)*nominal N L i.val a ≤ offsite anchor q b :=
by
  obtain ⟨N₀,h⟩ := PaperP1.UnconditionalPrintedAnchorObstruction.companion_T19_17 C D a hD ha ha1 η hη
  refine ⟨N₀,?_⟩
  intro N hN L E M i hwidth hM hband anchor A q hq b
  rw [offsite_eq A q hq b]
  exact h N hN L E M i hwidth hM hband anchor (toSource A) b

/-- The complete randomized T19.17 obstruction, with the exact extra one half.
The auxiliary probability space is arbitrary and independent of prime signs.
Orientations may depend on the source word and auxiliary sample. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.private_obstruction_randomized_obstruction (C D a : ℝ) (hD : 0 ≤ D)
    (ha : 0 < a) (ha1 : a < 1/10) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L+E+2 : ℕ) : ℝ) ≤ D*Real.log N → 2*N+(L+E+2) ≤ M →
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      ∀ anchor : retained N (L+E+2) (2*(L+E+2)) → Fin (L+i.val+1),
      ∀ _field : HybridData M (2*(L+E+2)) (L+i.val)
        (retained N (L+E+2) (2*(L+E+2))) (fullGood N (L+E+2) (cutoff N)) anchor,
      ∀ q : ∀ j : retained N (L+E+2) (2*(L+E+2)),
        j.val ∈ fullGood N (L+E+2) (cutoff N) → Fin (L+i.val+1) → PrimeUpTo M,
      (∀ j hj k, (q j hj k).val.val=largestOddPrime (j.val+k.val)) →
      ∀ (Ξ : Type*) [MeasurableSpace Ξ], ∀ μ : Measure Ξ, ∀ [IsProbabilityMeasure μ],
      ∀ b : Fin (L+i.val+1) → F₂,
      ∀ g : retained N (L+E+2) (2*(L+E+2)) → (Fin (L+i.val+1) → F₂) → Ξ → F₂,
      ∀ F : retained N (L+E+2) (2*(L+E+2)) → Sample M → Ξ → Sample M,
      (∀ j u s, MeasurableSet {ξ : Ξ | g j u ξ=s}) →
      (∀ j ω r s, MeasurableSet {ξ : Ξ | F j ω ξ r=s}) →
      (∀ j, j.val ∈ fullGood N (L+E+2) (cutoff N) → ∀ ω ξ,
        rawWord j.val (F j ω ξ)=fun k ↦ b k+g j (rawWord j.val ω) ξ) →
      (∀ j, ∀ hj : j.val ∈ fullGood N (L+E+2) (cutoff N), ∀ ω ξ, ∀ r : PrimeUpTo M,
        (∀ k, r ≠ q j hj k) → F j ω ξ r=ω r) →
      (1-η)/2*nominal N L i.val a ≤ randomizedOffsite μ b F :=
by
  obtain ⟨N₀,h⟩ := PaperP1.UnconditionalPrintedAnchorObstruction.companion_T19_17_randomized C D a hD ha ha1 η hη
  refine ⟨N₀,?_⟩
  intro N hN L E M i hwidth hM hband anchor A q hq Ξ _ μ _ b g F hg hF hhit hout
  have heq : q = PaperP1.RandomizedHybridField.fullPivots (hybridToSource A) := by
    funext j hj k
    apply Subtype.ext
    apply Fin.ext
    exact hq j hj k
  rw [randomizedOffsite_eq]
  apply h N hN L E M i hwidth hM hband anchor (hybridToSource A) Ξ μ b g F hg hF hhit
  intro j hj ω ξ r hr
  apply hout j hj ω ξ r
  intro k
  rw [heq]
  exact hr k

end PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction

end ComponentPrivateObstruction
