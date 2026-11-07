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

/-- All falling-factorial observables are genuinely integrable, and their
subset expansion uses the actual joint probabilities of the original starts. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_factorial_source (N L r : ℕ) :
    Integrable (fun ω ↦ ((runCount N L ω).descFactorial r : ℝ)) primeSignMeasure ∧
    factorialMoment N L r=(r.factorial : ℝ)*
      ∑ A ∈ (Ico N (2*N)).powersetCard r, jointMoment L A :=
by sorry

/-- Exact third-cumulant identity, including every heterogeneous marginal
and repeated-index correction, at all finite scales. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_third_exact_identity (N L : ℕ) :
    thirdCumulant N L=
      6*(∑ A ∈ (Ico N (2*N)).powersetCard 3, centeredCoefficient L A)-
      6*(∑ e ∈ (Ico N (2*N)).powersetCard 2,
        (∑ x ∈ e, marginal x L)*centeredCoefficient L e)+
      2*∑ x ∈ Ico N (2*N), (marginal x L)^3 :=
by sorry

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
by sorry

/-- Full critical-band equivalent of the actual second factorial cumulant,
with the exact moving residue coefficient and nominal mean. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_principal_second_equivalent (C τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      0 < principalSecondScale N L ∧ |secondCumulant N L/principalSecondScale N L-1| ≤ τ :=
by sorry

/-- The optimal positive 41/30 power for the actual third factorial cumulant.
The positive lower constant depends only on C, before the upper margin. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.factorial_cumulants_optimal_third_cumulant (C : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ)-Real.log N/Real.log 2| ≤ C →
      c*(N : ℝ)^(-41/30 : ℝ) ≤ thirdCumulant N L ∧
        thirdCumulant N L ≤ (N : ℝ)^(-41/30+ε) :=
by sorry

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

/-- Genuine probability masses with a uniform pointwise comparison.
The construction remains nonnegative throughout the full interval [0,2]. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_normalized_probabilities (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    HasSum (qMass a) 1 ∧ HasSum (pMass m a) 1 ∧
    ∀ k : ℕ, 0 ≤ qMass a k ∧ 0 ≤ pMass m a k ∧
      qMass a k/2 ≤ pMass m a k ∧ pMass m a k ≤ 3/2*qMass a k :=
by sorry

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
by sorry

/-- Exact positive total variation and the original uniform exponential-moment
bound, with absolute distance and exponential-series summability explicit. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_distance_and_exponential (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Summable (fun k : ℕ ↦ |pMass m a k-qMass a k|) ∧
    totalVariation m a=(1-a/2)*(2 : ℝ)^(m-2)/(Real.exp 1*(m.factorial : ℝ)) ∧
    ∀ t : ℝ, Summable (fun k : ℕ ↦ pMass m a k*Real.exp (t*k)) ∧
      (∑' k : ℕ, pMass m a k*Real.exp (t*k)) ≤
        3/2*Real.exp (Real.exp t-1)*(1+(1/2)*(Real.exp t-1)^2) :=
by sorry

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
by sorry

/-- The genuine probability-model distance exceeds every fixed polynomial
rate. Its explicit logarithmic error is uniform over all a in [0,1]. -/
theorem _root_.PaperP1Registry.Registration.CumulantsObstructions.moment_obstruction_uniform_subpolynomial (γ : ℝ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, 3 ≤ order N ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (N : ℝ)^(-γ) < totalVariation (order N) a ∧
        |Real.log (totalVariation (order N) a)+
          (1/2)*Real.sqrt (Real.log N)*Real.log (Real.log N)| ≤ 3*Real.sqrt (Real.log N) :=
by sorry

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
by sorry

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
by sorry

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
by sorry

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
by sorry

end PaperP1Registry.RegistrationModels.CumulantsObstructions.PrivateObstruction

end ComponentPrivateObstruction
