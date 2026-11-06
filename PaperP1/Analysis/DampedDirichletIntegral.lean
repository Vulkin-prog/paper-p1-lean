module

public import PaperP1.Analysis.DirichletPolynomialMeanValue
public import PaperP1.Analysis.ValuationDamping

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.DampedDirichletIntegral
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase GaussianExponentialSums DirichletPolynomialMeanValue
open scoped Classical

theorem coefficient_integral (P : Finset ℕ) (f : ℕ →* ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∫ z in (0 : ℝ)..1, (ValuationDamping.damped P f z n : ℂ))=
      (f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ) := by
  rw [intervalIntegral.integral_ofReal,ValuationDamping.damped_integral P f n hn,
    Complex.ofReal_div]
  norm_cast

theorem weighted_sum_continuous (S P : Finset ℕ) (f : ℕ →* ℝ) (b : ℕ → ℂ) :
    Continuous (fun z : ℝ ↦ ∑ n ∈ S, (ValuationDamping.damped P f z n : ℂ)*b n) := by
  apply continuous_finsetSum
  intro n hn
  exact (Complex.continuous_ofReal.comp (ValuationDamping.damped_continuous P f n)).mul continuous_const

theorem weighted_sum_integral (S P : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (f : ℕ →* ℝ) (b : ℕ → ℂ) :
    (∫ z in (0 : ℝ)..1, ∑ n ∈ S, (ValuationDamping.damped P f z n : ℂ)*b n)=
      ∑ n ∈ S, ((f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ))*b n := by
  have hc (n : ℕ) : Continuous (fun z : ℝ ↦ (ValuationDamping.damped P f z n : ℂ)*b n) :=
    (Complex.continuous_ofReal.comp (ValuationDamping.damped_continuous P f n)).mul continuous_const
  rw [intervalIntegral.integral_finsetSum (fun (n : ℕ) _hn ↦ (hc n).intervalIntegrable 0 1)]
  apply sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_mul_const,coefficient_integral P f n (hS n hn)]

theorem value_integral (S P : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0)
    (f : ℕ →* ℝ) (t : ℝ) :
    (∫ z in (0 : ℝ)..1, value S (fun n ↦ (ValuationDamping.damped P f z n : ℂ)) t)=
      value S (fun n ↦ (f n : ℂ)/((ValuationDamping.multiplicity P n+1 : ℕ) : ℂ)) t := by
  simpa only [value,polynomial,div_eq_mul_inv,mul_assoc] using
    weighted_sum_integral S P hS f (fun n ↦ (n : ℂ)⁻¹*phase (-Real.log n) t)

theorem squarefree_value_integral (S P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, n ≠ 0) (hsq : ∀ n ∈ S, ∀ p ∈ P, ¬p^2 ∣ n)
    (f : ℕ →* ℝ) (t : ℝ) :
    (∫ z in (0 : ℝ)..1, value S (fun n ↦ (ValuationDamping.damped P f z n : ℂ)) t)=
      value S (fun n ↦ (f n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)) t := by
  rw [value_integral S P hS f t]
  unfold value polynomial
  apply sum_congr rfl
  intro n hn
  dsimp only
  rw [ValuationDamping.multiplicity_eq_count P hP n (hS n hn) (hsq n hn)]
end PaperP1.DampedDirichletIntegral
