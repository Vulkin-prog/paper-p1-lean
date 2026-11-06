module

public import PaperP1.Analysis.CommonCutoffSurfaceBudget
public import PaperP1.Arithmetic.PrimePowerLogSeparation
public import PaperP1.Arithmetic.P3CanonicalSurfaceDivisor

/-! # An explicit optimized lower bound for the actual canonical global surface divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CanonicalDivisorLowerBound

open MvPolynomial Finset P3CanonicalSmoothResidues P3CanonicalSurfaceDivisor
open scoped Classical

variable {ι : Type*} [Fintype ι]

def smoothPopulation (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) : ℕ :=
  ∑ c, population p P v c

def commonCutoff (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) : Class p P → ℕ :=
  fun _ ↦ CommonCutoffSurfaceBudget.cutoff (Fintype.card (Class p P)) (smoothPopulation p P v)

def lowerBound (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) : ℝ :=
  (2 / 3 : ℝ) * smoothPopulation p P v *
    Real.sqrt (2 * (smoothPopulation p P v : ℝ) / (Fintype.card (Class p P) : ℝ)) -
      3 * smoothPopulation p P v

theorem exponent_lower_bound (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) :
    lowerBound p P v ≤ (exponent p P v (commonCutoff p P v) : ℝ) :=
  CommonCutoffSurfaceBudget.class_budget (fun c ↦ population p P v c)

theorem log_divisor (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) (L : ∀ p, Class p P → ℕ) :
    Real.log (divisor S P v L : ℝ) = ∑ p ∈ S, (exponent p P v (L p) : ℝ) * Real.log (p : ℝ) :=
  PrimePowerLogSeparation.log_product S hprimes (fun p ↦ exponent p P v (L p))

theorem log_divisor_lower_bound (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) :
    (∑ p ∈ S, lowerBound p P v * Real.log (p : ℝ)) ≤
      Real.log (divisor S P v (fun p ↦ commonCutoff p P v) : ℝ) := by
  rw [log_divisor S hprimes P v]
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (exponent_lower_bound p P v) (Real.log_natCast_nonneg p)

end PaperP1.P3CanonicalDivisorLowerBound
