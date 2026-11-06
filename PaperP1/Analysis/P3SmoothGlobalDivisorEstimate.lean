module

public import PaperP1.Analysis.P3BudgetedCanonicalDivisor
public import PaperP1.Arithmetic.P3CanonicalGradientPrimeLoss
public import PaperP1.Arithmetic.P3CoarseCanonicalClassCount

/-! # Original smooth integer points have a fully explicit global divisor estimate from coefficients, heights and prime sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3SmoothGlobalDivisorEstimate

open MvPolynomial Finset P3CanonicalSmoothResidues P3CanonicalSurfaceDivisor
open scoped Classical

def lowerBound (d s A H : ℕ) (D K : ℝ) (S : Finset ℕ) : ℝ :=
  Real.sqrt (2 * (s : ℝ) / D) *
    ((2 / 3 : ℝ) * s * (∑ p ∈ S, Real.log (p : ℝ) / p) - (s : ℝ) *
      (Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * A) : ℕ) : ℝ) +
        ((d - 1 : ℕ) : ℝ) * Real.log (H : ℝ)) / K) -
    3 * s * (∑ p ∈ S, Real.log (p : ℝ))

variable {ι : Type*} [Fintype ι]

theorem log_divisor_lower_bound (D : ℝ) (hD : 0 < D)
    (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (d A H : ℕ) (hd : 0 < d) (hA : 0 < A) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) (v : ι → Fin 4 → ℤ)
    (hnormal : ∀ j, v j 3 = 1) (hheight : ∀ j k, |v j k| ≤ (H : ℤ))
    (hroots : ∀ j, eval (v j) P = 0) (hgrad : ∀ j, ∃ k, eval (v j) (pderiv k P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ))
    (hclass : ∀ p ∈ S, (Fintype.card (Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2) :
    lowerBound d (Fintype.card ι) A H D K S ≤
      Real.log (divisor S P v (fun p ↦ P3BudgetedCanonicalDivisor.cutoffs D (Fintype.card ι) p P) : ℝ) := by
  have hb := P3BudgetedCanonicalDivisor.log_divisor_lower_bound D hD S hprimes P v hclass
  have hl := P3CanonicalGradientPrimeLoss.smooth_points_loss S hprimes d A H hd hA hH P hhom hcoef
    v hnormal hheight hroots hgrad K hK hlarge
  have hh := mul_le_mul_of_nonneg_left
    (sub_le_sub_left hl ((2 / 3 : ℝ) * Fintype.card ι * (∑ p ∈ S, Real.log (p : ℝ) / p)))
    (Real.sqrt_nonneg (2 * (Fintype.card ι : ℝ) / D))
  exact (sub_le_sub_right hh (3 * Fintype.card ι * (∑ p ∈ S, Real.log (p : ℝ)))).trans hb

theorem coarse_log_divisor_lower_bound
    (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (d A H : ℕ) (hd : 0 < d) (hA : 0 < A) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) (v : ι → Fin 4 → ℤ)
    (hnormal : ∀ j, v j 3 = 1) (hheight : ∀ j k, |v j k| ≤ (H : ℤ))
    (hroots : ∀ j, eval (v j) P = 0) (hgrad : ∀ j, ∃ k, eval (v j) (pderiv k P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    lowerBound d (Fintype.card ι) A H d K S ≤
      Real.log (divisor S P v (fun p ↦ P3BudgetedCanonicalDivisor.cutoffs d (Fintype.card ι) p P) : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply log_divisor_lower_bound (d : ℝ) hdR S hprimes d A H hd hA hH P hhom hcoef v
    hnormal hheight hroots hgrad K hK hlarge
  intro p hp
  exact_mod_cast P3CoarseCanonicalClassCount.cardinality_bound p d (hprimes p hp) P hhom

end PaperP1.P3SmoothGlobalDivisorEstimate
