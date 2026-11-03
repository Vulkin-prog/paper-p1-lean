module

public import PaperP1.Arithmetic.LogBudgetEuler
public import PaperP1.Arithmetic.WindowEulerAverage

/-! # Actual prime-set covers give multiplicative Euler bounds without disjointness assumptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EulerPrimeCovers

open Finset PaperP1.SmoothSquarefreeCount

theorem mono {P Q : Finset ℕ} (hPQ : P ⊆ Q) : eulerProduct P (1 / 2) ≤ eulerProduct Q (1 / 2) := by
  apply prod_le_prod_of_subset_of_one_le₀ hPQ
  · intro p _
    have h : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    linarith only [h]
  · intro p _ _
    have h : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    linarith only [h]

theorem biUnion {ι : Type*} (I : Finset ι) (Q : ι → Finset ℕ) :
    eulerProduct (I.biUnion Q) (1 / 2) ≤ ∏ i ∈ I, eulerProduct (Q i) (1 / 2) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [eulerProduct]
  | @insert i I hi ih =>
    rw [biUnion_insert, prod_insert hi]
    exact (LogBudgetEuler.euler_union (Q i) (I.biUnion Q)).trans
      (mul_le_mul_of_nonneg_left ih (eulerProduct_nonneg _ _))

theorem cover {ι : Type*} (P base : Finset ℕ) (I : Finset ι) (Q : ι → Finset ℕ)
    (hcover : P ⊆ base ∪ I.biUnion Q) :
    eulerProduct P (1 / 2) ≤ eulerProduct base (1 / 2) * ∏ i ∈ I, eulerProduct (Q i) (1 / 2) := by
  exact (mono hcover).trans ((LogBudgetEuler.euler_union base (I.biUnion Q)).trans
    (mul_le_mul_of_nonneg_left (biUnion I Q) (eulerProduct_nonneg _ _)))

theorem local_one_le (P : Finset ℕ) (n : ℕ) :
    1 ≤ FiniteEulerAverage.localProduct P RoughEulerMoments.halfWeight n :=
  LogBudgetEuler.euler_one_le (P.filter fun p ↦ p ∣ n)

theorem window_one_le (P : Finset ℕ) (B x : ℕ) : 1 ≤ WindowEulerAverage.windowProduct P B x :=
  one_le_prod₀ (fun _ _ ↦ local_one_le P _)

end PaperP1.EulerPrimeCovers
