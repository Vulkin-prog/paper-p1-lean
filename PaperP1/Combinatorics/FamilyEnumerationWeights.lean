module

public import PaperP1.Combinatorics.FamilyEnumerationUpper

/-! # Arbitrary nonnegative family weights retain the exact fixed-order factorial enumeration bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FamilyEnumerationWeights

open Finset PaperP1.FiniteFamilyEnumeration

theorem weighted_bound {r : ℕ} (F : Finset (Finset ℕ)) (P : Finset (Fin r → ℕ))
    (w : Finset ℕ → ℝ) (hw : ∀ I, 0 ≤ w I) (hF : ∀ I ∈ F, I.card = r)
    (hP : ∀ n ∈ P, Function.Injective n ∧ tupleSet n ∈ F) :
    (∑ n ∈ P, w (tupleSet n)) ≤ (r.factorial : ℝ) * ∑ I ∈ F, w I := by
  classical
  have hsplit := sum_fiberwise_of_maps_to (s := P) (t := F) (g := tupleSet)
    (fun n hn ↦ (hP n hn).2) (fun n ↦ w (tupleSet n))
  calc
    _ = ∑ I ∈ F, ∑ n ∈ P.filter (fun n ↦ tupleSet n = I), w (tupleSet n) := hsplit.symm
    _ ≤ ∑ I ∈ F, (r.factorial : ℝ) * w I := by
      apply sum_le_sum
      intro I hI
      let PI := P.filter fun n ↦ tupleSet n = I
      have hcount : PI.card ≤ r.factorial := by
        have h := FamilyEnumerationUpper.factorial_count_ge {I} PI (by
          intro J hJ
          simpa only [mem_singleton.mp hJ] using hF I hI) (by
          intro n hn
          obtain ⟨hnP, hset⟩ := mem_filter.mp hn
          exact ⟨(hP n hnP).1, mem_singleton.mpr hset⟩)
        simpa only [card_singleton, one_mul] using h
      have heq : (∑ n ∈ PI, w (tupleSet n)) = (PI.card : ℝ) * w I := by
        calc
          _ = ∑ _n ∈ PI, w I := sum_congr rfl (fun n hn ↦ congrArg w (mem_filter.mp hn).2)
          _ = _ := by rw [sum_const, nsmul_eq_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (hw I)
    _ = _ := by rw [mul_sum]

end PaperP1.FamilyEnumerationWeights
