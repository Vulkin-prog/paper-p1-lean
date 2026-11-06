module

public import PaperP1.Algebra.SurfaceEvaluationDeterminantDivisibility

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassifiedSurfaceDeterminantBudget

open Finset WeightedEvaluationDeterminant

variable {ι κ χ : Type*} [Fintype ι] [DecidableEq ι] [Fintype χ] [DecidableEq χ]

omit [DecidableEq ι] in
theorem classified_degree_budget (a : κ → χ) (m : κ → ℕ × ℕ)
    (hm : Function.Injective (fun r ↦ (a r, m r))) (b : ι → χ) (L : χ → ℕ)
    (f : ι → κ) (hf : Function.Injective f) (σ : Equiv.Perm ι)
    (hmatch : ∀ j, a (f (σ j)) = b j) :
    (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ≤
      ∑ i, ((m (f i)).1 + (m (f i)).2) := by
  classical
  have hc (c : χ) : L c * Fintype.card {j // b j = c} - (L c + 2).choose 3 ≤
      ∑ j : {j // b j = c}, ((m (f (σ j.val))).1 + (m (f (σ j.val))).2) := by
    have hi : Function.Injective (fun j : {j // b j = c} ↦ m (f (σ j.val))) := by
      intro j k he
      apply Subtype.ext
      apply σ.injective
      apply hf
      apply hm
      exact Prod.ext ((hmatch j.val).trans (j.property.trans (k.property.symm.trans (hmatch k.val).symm))) he
    have hh := BivariateMonomialDegreeBudget.total_degree_budget
      (fun j : {j // b j = c} ↦ m (f (σ j.val))) hi (L c)
    exact Nat.sub_le_iff_le_add.mpr (by simpa only [Nat.add_comm] using hh)
  have hh := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset χ)) ↦ hc c)
  calc
    _ ≤ _ := hh
    _ = ∑ j, ((m (f (σ j))).1 + (m (f (σ j))).2) :=
      Fintype.sum_fiberwise b (fun j ↦ (m (f (σ j))).1 + (m (f (σ j))).2)
    _ = _ := Equiv.sum_comp σ (fun i ↦ (m (f i)).1 + (m (f i)).2)

variable {R : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
theorem selected_dvd (p : R) (V : κ → ι → R) (a : κ → χ) (m : κ → ℕ × ℕ)
    (hm : Function.Injective (fun r ↦ (a r, m r))) (b : ι → χ) (L : χ → ℕ)
    (hV : ∀ r j, p ^ ((m r).1 + (m r).2) ∣ V r j)
    (hzero : ∀ r j, a r ≠ b j → V r j = 0)
    (f : ι → κ) (hf : Function.Injective f) :
    p ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ∣
      (selectedMatrix V f).det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  by_cases hmatch : ∀ j, a (f (σ j)) = b j
  · have hp : (∏ j, p ^ ((m (f (σ j))).1 + (m (f (σ j))).2)) ∣
        ∏ j, V (f (σ j)) j := Finset.prod_dvd_prod_of_dvd
      (fun j ↦ p ^ ((m (f (σ j))).1 + (m (f (σ j))).2))
      (fun j ↦ V (f (σ j)) j) (fun j _ ↦ hV (f (σ j)) j)
    rw [Finset.prod_pow_eq_pow_sum,
      Equiv.sum_comp σ (fun i ↦ (m (f i)).1 + (m (f i)).2)] at hp
    exact dvd_mul_of_dvd_right
      ((pow_dvd_pow p (classified_degree_budget a m hm b L f hf σ hmatch)).trans hp) _
  · obtain ⟨j, hj⟩ := Classical.not_forall.mp hmatch
    have hz : (selectedMatrix V f) (σ j) j = 0 := hzero (f (σ j)) j hj
    have hzprod : (∏ i, (selectedMatrix V f) (σ i) i) = 0 :=
      Finset.prod_eq_zero (mem_univ j) hz
    rw [hzprod, mul_zero]
    exact dvd_zero _

theorem evaluation_dvd (p : R) (C : ι → κ → R) (V : κ → ι → R)
    (a : κ → χ) (m : κ → ℕ × ℕ) (hm : Function.Injective (fun r ↦ (a r, m r)))
    (b : ι → χ) (L : χ → ℕ)
    (hV : ∀ r j, p ^ ((m r).1 + (m r).2) ∣ V r j)
    (hzero : ∀ r j, a r ≠ b j → V r j = 0) :
    p ^ (∑ c, (L c * Fintype.card {j // b j = c} - (L c + 2).choose 3)) ∣
      (evaluationMatrix C V).det := by
  classical
  rw [determinant_injective_expansion]
  apply Finset.dvd_sum
  intro f hf
  exact dvd_mul_of_dvd_right (selected_dvd p V a m hm b L hV hzero f (mem_filter.mp hf).2) _

end PaperP1.ClassifiedSurfaceDeterminantBudget
