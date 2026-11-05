module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.Push
public import Lean.Elab.Tactic.Omega

/-! # A nonzero polynomial over a characteristic-zero field avoids a bounded integer -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedFieldPolynomialNonvanishing

open Polynomial Finset

theorem exists_nat_nonroot {F : Type*} [Field F] [CharZero F]
    (q : F[X]) (hq : q ≠ 0) (D : ℕ) (hdegree : q.natDegree ≤ D) :
    ∃ t : ℕ, t ≤ D ∧ q.eval (t : F) ≠ 0 := by
  classical
  by_contra hn
  have hz : ∀ t : ℕ, t ≤ D → q.eval (t : F) = 0 := by
    intro t ht
    by_contra hne
    exact hn ⟨t, ht, hne⟩
  let S : Finset F := (range (D + 1)).image (fun t : ℕ ↦ (t : F))
  have hsub : S.val ⊆ q.roots := by
    intro z hzS
    obtain ⟨t, ht, rfl⟩ := mem_image.mp (show z ∈ S from hzS)
    exact (Polynomial.mem_roots hq).mpr (hz t (by have hh := mem_range.mp ht; omega))
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  have hcard : S.card = D + 1 := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
  omega

end PaperP1.BoundedFieldPolynomialNonvanishing
