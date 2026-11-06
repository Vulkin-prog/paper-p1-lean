module

public import PaperP1.Arithmetic.P3CanonicalSurfaceDivisor
public import PaperP1.Arithmetic.WeightedExceptionalPrimeFibres
public import PaperP1.Algebra.P3HomogeneousDerivativeHeight

/-! # The actual gradient-divisible columns have a proved weighted prime-loss bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3CanonicalGradientPrimeLoss

open MvPolynomial Finset
open scoped Classical

variable {ι : Type*} [Fintype ι]

theorem weighted_loss (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) (hnormal : ∀ j, v j 3 = 1)
    (hroots : ∀ j, eval (v j) P = 0) (k : ι → Fin 4)
    (hk : ∀ j, eval (v j) (pderiv (k j) P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    (∑ p ∈ S, (Fintype.card {j // P3CanonicalSurfaceDivisor.atPrime p P (v j) = none} : ℝ) *
      (Real.log (p : ℝ) / p)) ≤
      (∑ j, Real.log ((eval (v j) (pderiv (k j) P)).natAbs : ℝ)) / K := by
  have hdiv : ∀ p ∈ S, ∀ j, P3CanonicalSurfaceDivisor.atPrime p P (v j) = none →
      (p : ℤ) ∣ eval (v j) (pderiv (k j) P) := by
    intro p hp j hbad
    exact ((P3CanonicalSurfaceDivisor.unassigned_iff p (hprimes p hp) P (v j)
      (hnormal j) (hroots j)).mp hbad) (k j)
  have hh := WeightedExceptionalPrimeFibres.weighted_loss S hprimes
    (fun p j ↦ P3CanonicalSurfaceDivisor.atPrime p P (v j) = none)
    (fun j ↦ eval (v j) (pderiv (k j) P)) hk hdiv K hK hlarge
  simpa only [Nat.card_eq_fintype_card] using hh

theorem uniform_height_loss (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (P : MvPolynomial (Fin 4) ℤ) (v : ι → Fin 4 → ℤ) (hnormal : ∀ j, v j 3 = 1)
    (hroots : ∀ j, eval (v j) P = 0) (k : ι → Fin 4)
    (hk : ∀ j, eval (v j) (pderiv (k j) P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ))
    (A H m : ℕ) (hA : 0 < A) (hH : 1 ≤ H)
    (hbound : ∀ j, (eval (v j) (pderiv (k j) P)).natAbs ≤ A * H ^ m) :
    (∑ p ∈ S, (Fintype.card {j // P3CanonicalSurfaceDivisor.atPrime p P (v j) = none} : ℝ) *
      (Real.log (p : ℝ) / p)) ≤
      (Fintype.card ι : ℝ) * (Real.log (A : ℝ) + (m : ℝ) * Real.log (H : ℝ)) / K := by
  have hdiv : ∀ p ∈ S, ∀ j, P3CanonicalSurfaceDivisor.atPrime p P (v j) = none →
      (p : ℤ) ∣ eval (v j) (pderiv (k j) P) := by
    intro p hp j hbad
    exact ((P3CanonicalSurfaceDivisor.unassigned_iff p (hprimes p hp) P (v j)
      (hnormal j) (hroots j)).mp hbad) (k j)
  have hh := WeightedExceptionalPrimeFibres.uniform_height_loss S hprimes
    (fun p j ↦ P3CanonicalSurfaceDivisor.atPrime p P (v j) = none)
    (fun j ↦ eval (v j) (pderiv (k j) P)) hk hdiv K hK hlarge A H m hA hH hbound
  simpa only [Nat.card_eq_fintype_card] using hh

theorem coefficient_height_loss (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (d A H : ℕ) (hd : 0 < d) (hA : 0 < A) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) (v : ι → Fin 4 → ℤ)
    (hnormal : ∀ j, v j 3 = 1) (hheight : ∀ j k, |v j k| ≤ (H : ℤ))
    (hroots : ∀ j, eval (v j) P = 0) (k : ι → Fin 4)
    (hk : ∀ j, eval (v j) (pderiv (k j) P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    (∑ p ∈ S, (Fintype.card {j // P3CanonicalSurfaceDivisor.atPrime p P (v j) = none} : ℝ) *
      (Real.log (p : ℝ) / p)) ≤
      (Fintype.card ι : ℝ) *
        (Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * A) : ℕ) : ℝ) +
          ((d - 1 : ℕ) : ℝ) * Real.log (H : ℝ)) / K := by
  apply uniform_height_loss S hprimes P v hnormal hroots k hk K hK hlarge
    (Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * A)) H (d - 1)
    (Nat.mul_pos (P3HomogeneousIntegerInterpolation.index_card_pos _) (Nat.mul_pos hd hA)) hH
  intro j
  exact P3HomogeneousDerivativeHeight.derivative_value_bound d A H P hhom hcoef (v j) (hheight j) (k j)

theorem smooth_points_loss (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (d A H : ℕ) (hd : 0 < d) (hA : 0 < A) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hhom : P.IsHomogeneous d)
    (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ)) (v : ι → Fin 4 → ℤ)
    (hnormal : ∀ j, v j 3 = 1) (hheight : ∀ j k, |v j k| ≤ (H : ℤ))
    (hroots : ∀ j, eval (v j) P = 0) (hgrad : ∀ j, ∃ k, eval (v j) (pderiv k P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ)) :
    (∑ p ∈ S, (Fintype.card {j // P3CanonicalSurfaceDivisor.atPrime p P (v j) = none} : ℝ) *
      (Real.log (p : ℝ) / p)) ≤
      (Fintype.card ι : ℝ) *
        (Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * A) : ℕ) : ℝ) +
          ((d - 1 : ℕ) : ℝ) * Real.log (H : ℝ)) / K := by
  choose k hk using hgrad
  exact coefficient_height_loss S hprimes d A H hd hA hH P hhom hcoef v hnormal hheight hroots
    k hk K hK hlarge

end PaperP1.P3CanonicalGradientPrimeLoss
