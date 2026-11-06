module

public import PaperP1.Algebra.FilteredEvaluationDeterminantDivisibility
public import PaperP1.Algebra.BivariateMonomialDegreeBudget
public import Mathlib.Tactic.Ring

/-! # Exact determinant divisibility for actual monomials in two free coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SurfaceEvaluationDeterminantDivisibility

open Finset WeightedEvaluationDeterminant FilteredEvaluationDeterminantDivisibility

variable {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem selected_budget_dvd (p : R) (C : ι → κ → R) (V : κ → ι → R) (w : κ → ℕ) (E : ℕ)
    (hV : ∀ r j, p ^ w r ∣ V r j)
    (hbudget : ∀ f : ι → κ, Function.Injective f → E ≤ ∑ i, w (f i)) :
    p ^ E ∣ (evaluationMatrix C V).det := by
  classical
  rw [determinant_injective_expansion]
  apply Finset.dvd_sum
  intro f hf
  have hi : Function.Injective f := (mem_filter.mp hf).2
  have hd := row_power_dvd p (selectedMatrix V f) (fun i ↦ w (f i)) (fun i j ↦ hV (f i) j)
  exact dvd_mul_of_dvd_right ((pow_dvd_pow p (hbudget f hi)).trans hd) _

theorem bivariate_dvd (p : R) (C : ι → κ → R) (V : κ → ι → R) (m : κ → ℕ × ℕ)
    (hm : Function.Injective m) (L : ℕ) (hV : ∀ r j, p ^ ((m r).1 + (m r).2) ∣ V r j) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ (evaluationMatrix C V).det := by
  apply selected_budget_dvd p C V (fun r ↦ (m r).1 + (m r).2) _ hV
  intro f hf
  have hh := BivariateMonomialDegreeBudget.total_degree_budget (m ∘ f) (hm.comp hf) L
  apply Nat.sub_le_iff_le_add.mpr
  simpa only [Function.comp_apply, Nat.add_comm] using hh

theorem monomial_dvd (p : R) (C : ι → κ → R) (m : κ → ℕ × ℕ) (hm : Function.Injective m)
    (L : ℕ) (x y : ι → R) (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣
      (evaluationMatrix C (fun r j ↦ x j ^ (m r).1 * y j ^ (m r).2)).det := by
  apply bivariate_dvd p C _ m hm L
  intro r j
  obtain ⟨u, hu⟩ := hx j
  obtain ⟨v, hv⟩ := hy j
  refine ⟨u ^ (m r).1 * v ^ (m r).2, ?_⟩
  change x j ^ (m r).1 * y j ^ (m r).2 = p ^ ((m r).1 + (m r).2) * (u ^ (m r).1 * v ^ (m r).2)
  rw [hu, hv, mul_pow, mul_pow, pow_add]
  ring

theorem congruent_monomial_dvd (p : R) (C : ι → κ → R) (m : κ → ℕ × ℕ) (hm : Function.Injective m)
    (L : ℕ) (x y : ι → R) (hx : ∀ j, p ∣ x j) (hy : ∀ j, p ∣ y j) (A : Matrix ι ι R)
    (hA : ∀ i j, p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A i j -
      evaluationMatrix C (fun r j ↦ x j ^ (m r).1 * y j ^ (m r).2) i j) :
    p ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A.det := by
  have hd := determinant_congruence_dvd (p ^ (L * Fintype.card ι - (L + 2).choose 3)) A
    (evaluationMatrix C (fun r j ↦ x j ^ (m r).1 * y j ^ (m r).2)) hA
  have hh := dvd_add hd (monomial_dvd p C m hm L x y hx hy)
  simpa only [sub_add_cancel] using hh

end PaperP1.SurfaceEvaluationDeterminantDivisibility
