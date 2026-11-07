module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import PaperP1.Asymptotics.MomentObstructionSequence

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

theorem qMass_eq (a : ℝ) (k : ℕ) : qMass a k=PaperP1.MomentObstructionMass.qMass a k := by rfl

theorem qMass_fun_eq (a : ℝ) : qMass a=PaperP1.MomentObstructionMass.qMass a := funext (qMass_eq a)

theorem coefficient_eq (m k : ℕ) : differenceCoefficient m k=
    ((PaperP1.Probability.forwardDifference : PaperP1.Probability.SignedLaw ℝ)^m).coeff k :=
  (PaperP1.DifferenceCoefficients.forwardDifference_pow_coeff m k).symm

theorem epsilon_eq (m : ℕ) (a : ℝ) : epsilon m a=PaperP1.MomentObstructionMass.epsilon m a := by rfl

theorem pMass_eq (m : ℕ) (a : ℝ) (k : ℕ) : pMass m a k=PaperP1.MomentObstructionMass.pMass m a k := by
  simp only [pMass,qMass_eq,epsilon_eq,coefficient_eq,PaperP1.MomentObstructionMass.pMass]

theorem pMass_fun_eq (m : ℕ) (a : ℝ) : pMass m a=PaperP1.MomentObstructionMass.pMass m a := funext (pMass_eq m a)

theorem totalVariation_eq (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    totalVariation m a=PaperP1.MomentObstructionLog.distance m a := by
  have h := PaperP1.MomentObstruction.totalVariation_exact m (by omega) hm a ha0 ha2
  simp only [PaperP1.AtomicProbability.totalVariation,
    PaperP1.MomentObstructionMass.pLaw_real_singleton,
    PaperP1.MomentObstructionMass.qLaw_real_singleton] at h
  simpa only [totalVariation,pMass_eq,qMass_eq,PaperP1.MomentObstructionLog.distance] using h

theorem order_eq (N : ℕ) : order N=PaperP1.MomentObstructionSequence.order N := by rfl

theorem parameter_eq (N : ℕ) : parameter N=PaperP1.MomentObstructionSequence.parameter N := by rfl

theorem valid_eq (N : ℕ) : Valid N ↔ PaperP1.MomentObstructionSequence.Valid N := by rfl

/-- Genuine probability masses with a uniform pointwise comparison.
The construction remains nonnegative throughout the full interval [0,2]. -/
theorem normalized_probabilities (m : ℕ) (hm : 1 ≤ m) (a : ℝ)
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
by
  obtain ⟨hQn,hPn,hpos⟩ := normalized_probabilities m (by omega) a ha0 (by linarith)
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
theorem distance_and_exponential (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Summable (fun k : ℕ ↦ |pMass m a k-qMass a k|) ∧
    totalVariation m a=(1-a/2)*(2 : ℝ)^(m-2)/(Real.exp 1*(m.factorial : ℝ)) ∧
    ∀ t : ℝ, Summable (fun k : ℕ ↦ pMass m a k*Real.exp (t*k)) ∧
      (∑' k : ℕ, pMass m a k*Real.exp (t*k)) ≤
        3/2*Real.exp (Real.exp t-1)*(1+(1/2)*(Real.exp t-1)^2) :=
by
  obtain ⟨hQ,hP,_⟩ := normalized_probabilities m (by omega) a ha0 (by linarith)
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
theorem fixed_order_matching (r : ℕ) :
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
  obtain ⟨hqn,hpn,hpos,hseries⟩ := all_factorial_series (order N) hv.1 (parameter N) hv.2.1 hv.2.2
  obtain ⟨hq,hp,_hiff⟩ := hseries r
  exact ⟨hv,hpn,hqn,hpos,by simpa only [ite_eq_right hne,add_zero] using hp,hq⟩

/-- The genuine probability-model distance exceeds every fixed polynomial
rate. Its explicit logarithmic error is uniform over all a in [0,1]. -/
theorem uniform_subpolynomial (γ : ℝ) (hγ : 0 < γ) :
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

end PaperP1Registry.MomentObstruction
