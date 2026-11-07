module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import PaperP1.Analysis.QuadraticComparisonRange
public import PaperP1.Asymptotics.ActualQuadraticComparisonCounterexample

/-! # Prescribed squarefree kernels of shifted split products

These statements retain the actual integer and kernel bins, a positive
prescribed divisor, and the quantifier order of companion T5.1. The trivial
exponent cap repairs the original exact comparison. The uncapped counting
bound remains valid; its exact comparison is qualified, and the failure of
the unqualified display is witnessed on actual arbitrarily large data.
The Challenge uses only Mathlib. Its selected statement holes are not proof
evidence; the separate Solution supplies complete proofs.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.QuadraticKernels
open Finset
open scoped Classical

/-- Prime exponents reduced modulo two. -/
def oddFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e : ℕ ↦ e % 2) (by simp)

/-- The ordinary squarefree kernel: the product of primes of odd valuation.
It is one on squares. The totalized value at zero is unused at positive scale. -/
def squarefreeKernel (n : ℕ) : ℕ := (oddFactorization n).support.prod id

/-- The squarefree kernel of the actual shifted split product. -/
def kernel (h n : ℕ) : ℕ := squarefreeKernel (n*(n+h))

/-- The literal integer and kernel bins, with the prescribed divisor. -/
def values (N h e : ℕ) (β : ℝ) : Finset ℕ :=
  (Icc N (2*N)).filter fun n ↦ (N : ℝ)^β ≤ kernel h n ∧
    (kernel h n : ℝ) < 2*(N : ℝ)^β ∧ e ∣ kernel h n

/-- The minimum of the two arithmetic counting exponents. -/
def rawExponent (β δ : ℝ) : ℝ := min (β-δ) (max (β/2-δ) (1-β/2))

/-- The additional trivial O(N) cap, needed for a universal exact comparison. -/
def cappedExponent (β δ : ℝ) : ℝ := min 1 (rawExponent β δ)

/-- The affine exponent in the corrected prescribed-kernel lemma. -/
def affineExponent (β δ : ℝ) : ℝ := 1/2+β/4-δ/2

/-- All three actual counting bounds for positive polylogarithmic shifts and
positive prescribed divisors. One threshold precedes every shift, divisor and
real kernel exponent. An arbitrary fixed positive power margin is explicit. -/
theorem uniform_count (D A ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ,
      0 < h → 0 < e → (h : ℝ) ≤ D*(Real.log (N : ℝ))^A →
      ((values N h e β).card : ℝ) ≤
        (N : ℝ)^(rawExponent β (Real.log (e : ℝ)/Real.log (N : ℝ))+ε) ∧
      ((values N h e β).card : ℝ) ≤
        (N : ℝ)^(cappedExponent β (Real.log (e : ℝ)/Real.log (N : ℝ))+ε) ∧
      ((values N h e β).card : ℝ) ≤
        (N : ℝ)^(affineExponent β (Real.log (e : ℝ)/Real.log (N : ℝ))+ε) :=
by
  have hValues (N h e : ℕ) (β : ℝ) : values N h e β =
      PaperP1.PrescribedQuadraticKernelTheorem.values N h e β := by
    ext n
    simp [values, kernel, squarefreeKernel, oddFactorization,
      PaperP1.PrescribedQuadraticKernelTheorem.values, PaperP1.QuadraticKernelFibres.kernel,
      PaperP1.SmallPrimeBudget.squarefreeKernel, PaperP1.DefectivePredicate.oddPrimeSupport,
      PaperP1.DefectivePredicate.oddFactorization]
  obtain ⟨N₀,h₀⟩ := PaperP1.PrescribedQuadraticKernelTheorem.actual_exponent_counts D A ε hε
  refine ⟨max 2 N₀,le_max_left _ _,?_⟩
  intro N hN h e β hh he hShift
  simpa only [hValues, rawExponent, cappedExponent, affineExponent,
    PaperP1.QuadraticKernelExponents.exponent, PaperP1.QuadraticKernelExponents.capped,
    PaperP1.QuadraticKernelExponents.affine] using h₀ N (by omega) h e β hh he hShift

/-- The capped exact affine comparison holds for every pair of real parameters. -/
theorem capped_comparison (β δ : ℝ) : cappedExponent β δ ≤ affineExponent β δ :=
by
  simpa only [rawExponent,cappedExponent,affineExponent,
    PaperP1.QuadraticKernelExponents.exponent,PaperP1.QuadraticKernelExponents.capped,
    PaperP1.QuadraticKernelExponents.affine] using
    PaperP1.QuadraticKernelExponents.capped_le_affine β δ

/-- With nonnegative divisor exponent, the uncapped exact comparison has this
necessary and sufficient range. Actual positive divisors at N>=2 satisfy the
sign condition. Without it this range is sufficient but need not be necessary. -/
theorem uncapped_comparison_iff (β δ : ℝ) (hδ : 0 ≤ δ) :
    rawExponent β δ ≤ affineExponent β δ ↔ β-2*δ ≤ 2 :=
by
  simpa only [rawExponent,affineExponent,
    PaperP1.QuadraticKernelExponents.exponent,PaperP1.QuadraticKernelExponents.affine] using
    PaperP1.QuadraticComparisonRange.exponent_le_affine_iff_of_nonneg_delta β δ hδ

/-- The exact kernel exponent of N(N+1) at scale N. -/
def adjacentExponent (N : ℕ) : ℝ := Real.log ((N : ℝ)*((N : ℝ)+1))/Real.log (N : ℝ)

/-- The uncapped comparison in the original display fails on arbitrarily large
actual admissible data h=e=1, n=N, with consecutive squarefree N and N+1.
This refutes only the unrestricted exact comparison; all counting bounds above
remain valid. The shift obeys every nonnegative logarithmic power budget. -/
theorem actual_uncapped_counterexamples (M : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ N : ℕ, M < N ∧ 2 ≤ N ∧ Squarefree N ∧ Squarefree (N+1) ∧
      (1 : ℝ) ≤ (Real.log (N : ℝ))^A ∧
      N ∈ values N 1 1 (adjacentExponent N) ∧ 2 < adjacentExponent N ∧
      affineExponent (adjacentExponent N) 0 < rawExponent (adjacentExponent N) 0 :=
by
  have hValues (N h e : ℕ) (β : ℝ) : values N h e β =
      PaperP1.PrescribedQuadraticKernelTheorem.values N h e β := by
    ext n
    simp [values, kernel, squarefreeKernel, oddFactorization,
      PaperP1.PrescribedQuadraticKernelTheorem.values, PaperP1.QuadraticKernelFibres.kernel,
      PaperP1.SmallPrimeBudget.squarefreeKernel, PaperP1.DefectivePredicate.oddPrimeSupport,
      PaperP1.DefectivePredicate.oddFactorization]
  obtain ⟨Nlog,hLog⟩ := PaperP1.ElementaryLogGrowth.log_ge_eventually 1
  obtain ⟨N,hN,hSf,hNext⟩ := PaperP1.AdjacentSquarefreeCount.arbitrarily_large (max M (max 2 Nlog))
  have hN2 : 2 ≤ N := by omega
  refine ⟨N,by omega,hN2,hSf,hNext,
    Real.one_le_rpow (hLog N (by omega)).1 hA,?_,?_,?_⟩
  · rw [hValues]
    simpa only [adjacentExponent,PaperP1.ActualQuadraticComparisonCounterexample.beta] using
      PaperP1.ActualQuadraticComparisonCounterexample.source_value N hN2 hSf hNext
  · simpa only [adjacentExponent,PaperP1.ActualQuadraticComparisonCounterexample.beta] using
      PaperP1.ActualQuadraticComparisonCounterexample.beta_gt_two N hN2
  · simpa only [adjacentExponent,rawExponent,affineExponent,
      PaperP1.ActualQuadraticComparisonCounterexample.beta,
      PaperP1.QuadraticKernelExponents.exponent,PaperP1.QuadraticKernelExponents.affine] using
      PaperP1.ActualQuadraticComparisonCounterexample.comparison_failure N hN2

end PaperP1Registry.QuadraticKernels
