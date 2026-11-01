module

public import PaperP1.Model.PrescribedTupleMass
public import PaperP1.Combinatorics.TupleExtensions

/-! # Finite iteration of actual ordered-tuple mass bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TupleMassIteration

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass

theorem iterate {s r L : ℕ} (G : Finset ℕ) (c : ℕ → Fin L → F₂) (B : ℝ)
    (hs : 1 ≤ s) (hB : 0 ≤ B)
    (hstep : ∀ q : ℕ, 1 ≤ q → q ≤ r → ∀ F : Finset (Fin q → ℕ),
      (∀ x ∈ F, ∀ i, x i ∈ G) →
      (∑ y ∈ TupleExtensions.step G F, joint L c y) ≤ B * ∑ x ∈ F, joint L c x)
    (F : Finset (Fin s → ℕ)) (hF : ∀ x ∈ F, ∀ i, x i ∈ G) (k : ℕ) (hsize : s + k ≤ r) :
    (∑ y ∈ TupleExtensions.more G F k, joint L c y) ≤ B ^ k * ∑ x ∈ F, joint L c x := by
  induction k with
  | zero =>
      simp only [TupleExtensions.more, pow_zero, one_mul]
      exact @Preorder.le_refl ℝ Real.partialOrder.toPreorder _
  | succ k ih =>
    have hprevious := ih (by omega)
    have hcoordinates := TupleExtensions.more_coordinates G F hF k
    calc
      _ ≤ B * ∑ x ∈ TupleExtensions.more G F k, joint L c x :=
        hstep (s + k) (by omega) (by omega) _ hcoordinates
      _ ≤ B * (B ^ k * ∑ x ∈ F, joint L c x) := mul_le_mul_of_nonneg_left hprevious hB
      _ = _ := by rw [pow_succ]; ring

end PaperP1.TupleMassIteration
