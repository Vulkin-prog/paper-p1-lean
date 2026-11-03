module

public import PaperP1.Algebra.EvenImageEmbeddingDefect
public import PaperP1.Arithmetic.FiniteEvenSquareClasses

/-! # A literal subset of values inherits at most the full even square-class defect -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenSubsetRankDefect

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance evenSubsetRankPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem subset_defect {S T : Finset ℕ} (hST : S ⊆ T) :
    S.card - 1 ≤ Module.finrank F₂ (space S) + ((T.card - 1) - Module.finrank F₂ (space T)) := by
  let e : S ↪ T := ⟨fun n ↦ ⟨n.val, hST n.property⟩, by
    intro n m h
    exact Subtype.ext (congrArg (fun n : T ↦ (n : ℕ)) h)⟩
  have h := EvenImageEmbeddingDefect.image_defect_bound (K := F₂) e (data S) (data T) (fun _ ↦ rfl)
  simp only [Fintype.card_coe] at h
  with_unfolding_all exact h

end PaperP1.EvenSubsetRankDefect
