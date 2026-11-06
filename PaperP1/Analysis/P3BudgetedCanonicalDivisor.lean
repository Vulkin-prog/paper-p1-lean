module

public import PaperP1.Analysis.ExceptionalSurfaceClassBudget
public import PaperP1.Analysis.P3CanonicalDivisorLowerBound

/-! # A supplied numerical class budget yields an actual canonical determinant bound with every exceptional column paid -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3BudgetedCanonicalDivisor

open MvPolynomial Finset P3CanonicalSmoothResidues P3CanonicalSurfaceDivisor
open scoped Classical

def cutoffs (D : ℝ) (s p : ℕ) (P : MvPolynomial (Fin 4) ℤ) : Class p P → ℕ :=
  fun _ ↦ ExceptionalSurfaceClassBudget.cutoff (D * (p : ℝ) ^ 2) s

theorem sqrt_budget (D : ℝ) (hD : 0 < D) (s p : ℕ) (hp : 0 < p) :
    Real.sqrt (2 * (s : ℝ) / (D * (p : ℝ) ^ 2)) = Real.sqrt (2 * (s : ℝ) / D) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have he : 2 * (s : ℝ) / (D * (p : ℝ) ^ 2) = (2 * (s : ℝ) / D) / (p : ℝ) ^ 2 := by
    field_simp [hD.ne', hpR.ne']
  rw [he, Real.sqrt_div (by positivity), Real.sqrt_sq (Nat.cast_nonneg p)]

variable {ι : Type*} [Fintype ι]

theorem exponent_lower_bound (D : ℝ) (hD : 0 < D) (p : ℕ) (hp : p.Prime)
    (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ)
    (hclass : (Fintype.card (Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2) :
    Real.sqrt (2 * (Fintype.card ι : ℝ) / D) *
        ((2 / 3 : ℝ) * Fintype.card ι - Fintype.card {j // atPrime p P (v j) = none}) / p -
      3 * Fintype.card ι ≤ (exponent p P v (cutoffs D (Fintype.card ι) p P) : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hh := ExceptionalSurfaceClassBudget.class_budget (fun c ↦ population p P v c)
    (Fintype.card ι) (Fintype.card {j // atPrime p P (v j) = none})
    (total_population p P v) (D * (p : ℝ) ^ 2) (by positivity) hclass
  rw [sqrt_budget D hD (Fintype.card ι) p hp.pos] at hh
  change _ ≤ (exponent p P v (cutoffs D (Fintype.card ι) p P) : ℝ) at hh
  convert hh using 1; ring

theorem log_divisor_lower_bound (D : ℝ) (hD : 0 < D)
    (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ)
    (hclass : ∀ p ∈ S, (Fintype.card (Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2) :
    Real.sqrt (2 * (Fintype.card ι : ℝ) / D) *
        ((2 / 3 : ℝ) * Fintype.card ι * (∑ p ∈ S, Real.log (p : ℝ) / p) -
          ∑ p ∈ S, (Fintype.card {j // atPrime p P (v j) = none} : ℝ) * (Real.log (p : ℝ) / p)) -
      3 * Fintype.card ι * (∑ p ∈ S, Real.log (p : ℝ)) ≤
        Real.log (divisor S P v (fun p ↦ cutoffs D (Fintype.card ι) p P) : ℝ) := by
  let R := Real.sqrt (2 * (Fintype.card ι : ℝ) / D)
  let A : ℝ := (2 / 3 : ℝ) * Fintype.card ι
  let B : ℕ → ℝ := fun p ↦ Fintype.card {j // atPrime p P (v j) = none}
  have hterm (p : ℕ) (hp : p ∈ S) :
      R * (A * (Real.log (p : ℝ) / p) - B p * (Real.log (p : ℝ) / p)) -
        3 * Fintype.card ι * Real.log (p : ℝ) ≤
      (exponent p P v (cutoffs D (Fintype.card ι) p P) : ℝ) * Real.log (p : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (exponent_lower_bound D hD p (hprimes p hp) P v (hclass p hp))
      (Real.log_natCast_nonneg p)
    change R * (A * (Real.log (p : ℝ) / p) - B p * (Real.log (p : ℝ) / p)) -
      3 * Fintype.card ι * Real.log (p : ℝ) ≤ _
    convert hh using 1; dsimp only [R, A, B]; ring
  have hs := Finset.sum_le_sum (fun p (hp : p ∈ S) ↦ hterm p hp)
  have he : (∑ p ∈ S, (R * (A * (Real.log (p : ℝ) / p) - B p * (Real.log (p : ℝ) / p)) -
        3 * Fintype.card ι * Real.log (p : ℝ))) =
      R * (A * (∑ p ∈ S, Real.log (p : ℝ) / p) -
        ∑ p ∈ S, B p * (Real.log (p : ℝ) / p)) -
      3 * Fintype.card ι * (∑ p ∈ S, Real.log (p : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [he, ← P3CanonicalDivisorLowerBound.log_divisor S hprimes P v] at hs
  exact hs

end PaperP1.P3BudgetedCanonicalDivisor
