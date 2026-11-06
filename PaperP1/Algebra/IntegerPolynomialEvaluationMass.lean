module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Positivity

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPolynomialEvaluationMass

open MvPolynomial Finset

variable {σ : Type*}

def coefficientMass (P : MvPolynomial σ ℤ) : ℕ := ∑ m ∈ P.support, (P.coeff m).natAbs

def familyMass (forms : Finset (MvPolynomial σ ℤ)) : ℕ := 1 + ∑ P ∈ forms, coefficientMass P

def familyDegree (forms : Finset (MvPolynomial σ ℤ)) : ℕ := forms.sup MvPolynomial.totalDegree

theorem monomial_bound (m : σ →₀ ℕ) (v : σ → ℤ) (A : ℕ)
    (hv : ∀ k, |v k| ≤ (A : ℤ)) : |m.prod (fun k e ↦ v k ^ e)| ≤ (A : ℤ) ^ m.degree := by
  classical
  rw [Finsupp.prod, abs_prod]
  calc
    (∏ k ∈ m.support, |v k ^ m k|) ≤ ∏ k ∈ m.support, (A : ℤ) ^ m k := by
      apply Finset.prod_le_prod₀ (fun k _ ↦ abs_nonneg _)
      intro k _
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hv k) _
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]

theorem evaluation_bound (P : MvPolynomial σ ℤ) (A : ℕ) (hA : 1 ≤ A)
    (v : σ → ℤ) (hv : ∀ k, |v k| ≤ (A : ℤ)) :
    (eval v P).natAbs ≤ coefficientMass P * A ^ P.totalDegree := by
  classical
  have hAR : (1 : ℤ) ≤ A := by exact_mod_cast hA
  have hb : |eval v P| ≤ (coefficientMass P : ℤ) * (A : ℤ) ^ P.totalDegree := by
    rw [eval_eq]
    calc
      _ ≤ ∑ m ∈ P.support, |P.coeff m * ∏ k ∈ m.support, v k ^ m k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ P.support, ((P.coeff m).natAbs : ℤ) * (A : ℤ) ^ P.totalDegree := by
        apply Finset.sum_le_sum
        intro m hm
        have hd : m.degree ≤ P.totalDegree := le_totalDegree hm
        have hmono := (monomial_bound m v A hv).trans (pow_le_pow_right₀ hAR hd)
        rw [abs_mul, Int.natCast_natAbs]
        exact mul_le_mul_of_nonneg_left hmono (abs_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul]
        simp only [coefficientMass, Nat.cast_sum]
  have hb' : ((eval v P).natAbs : ℤ) ≤ ((coefficientMass P * A ^ P.totalDegree : ℕ) : ℤ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using hb
  exact_mod_cast hb'

theorem familyMass_pos (forms : Finset (MvPolynomial σ ℤ)) : 0 < familyMass forms := by
  dsimp only [familyMass]
  omega

theorem family_bound (forms : Finset (MvPolynomial σ ℤ)) (P : MvPolynomial σ ℤ) (hP : P ∈ forms)
    (A : ℕ) (hA : 1 ≤ A) (v : σ → ℤ) (hv : ∀ k, |v k| ≤ (A : ℤ)) :
    (eval v P).natAbs ≤ familyMass forms * A ^ familyDegree forms := by
  classical
  have hm₀ := Finset.single_le_sum (f := coefficientMass) (fun Q _ ↦ Nat.zero_le (coefficientMass Q)) hP
  have hm : coefficientMass P ≤ familyMass forms := by dsimp only [familyMass]; omega
  have hd : P.totalDegree ≤ familyDegree forms := Finset.le_sup hP
  exact (evaluation_bound P A hA v hv).trans (Nat.mul_le_mul hm (Nat.pow_le_pow_right hA hd))

end PaperP1.IntegerPolynomialEvaluationMass
