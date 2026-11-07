module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-! # Fixed-order moments do not imply a polynomial approximation rate
The actual probability masses, finite perturbation, all moment sums and
half-l1 distance are literal Mathlib expressions. The a=2 endpoint is retained
for positivity and excluded from the unique-changed-moment assertion. These
are constructed probability models, not the multiplicative-run count law.
Only the five selected Challenge theorem holes are deliberate placeholders.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1Registry.MomentObstruction
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
theorem normalized_probabilities (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    HasSum (qMass a) 1 ∧ HasSum (pMass m a) 1 ∧
    ∀ k : ℕ, 0 ≤ qMass a k ∧ 0 ≤ pMass m a k ∧
      qMass a k/2 ≤ pMass m a k ∧ pMass m a k ≤ 3/2*qMass a k :=
by sorry

/-- Every factorial moment exists as an unconditionally convergent mass sum.
In the original range [0,1], exactly order m changes, including among higher
orders; at a=2 the perturbation vanishes and that iff is not asserted. -/
theorem all_factorial_series (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
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
theorem distance_and_exponential (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
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
theorem fixed_order_matching (r : ℕ) :
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
theorem uniform_subpolynomial (γ : ℝ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, 3 ≤ order N ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (N : ℝ)^(-γ) < totalVariation (order N) a ∧
        |Real.log (totalVariation (order N) a)+
          (1/2)*Real.sqrt (Real.log N)*Real.log (Real.log N)| ≤ 3*Real.sqrt (Real.log N) :=
by sorry

end PaperP1Registry.MomentObstruction
