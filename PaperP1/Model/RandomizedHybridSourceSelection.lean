module

public import PaperP1.Model.RandomizedHybridSourceData

/-! # Simultaneous small quarter-flip source selection before any signs are drawn -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedHybridSourceSelection

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.RandomizedHybridField
  PaperP1.RandomizedHybridBoundaryPairs PaperP1.RandomizedHybridSourceData

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}

theorem exists_selector {Ξ : Type*} [Fintype Ξ] (D : Data M Y K G Good anchor)
    (P : PaperP1.Probability.FiniteProbability Ξ) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (J : Finset ℕ) (Q : ℝ)
    (hJ : J ⊆ G) (hactive : J ⊆ Good)
    (hOrd : ∀ j ∈ J, 2 ≤ (PaperP1.NonanchorPivotSelection.ordinaryIndices j (K + 1) Q).card) :
    ∃ selected : G → Fin (K + 1),
      (∀ j ∈ J, (selectedPrime D selected j : ℝ) ≤ Q) ∧
      (∀ j : ℕ, ∀ hj : j ∈ J, (1 / 4 : ℝ) ≤
        PaperP1.RandomizedSourceFlip.probability P b (g ⟨j, hJ hj⟩) (selected ⟨j, hJ hj⟩)) := by
  classical
  have hs : ∀ j : G, ∃ i : Fin (K + 1), j.val ∈ J →
      i ∈ PaperP1.NonanchorPivotSelection.ordinaryIndices j.val (K + 1) Q ∧
        (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b (g j) i := by
    intro j
    by_cases hj : j.val ∈ J
    · obtain ⟨i, hi, hq⟩ := PaperP1.RandomizedSourceFlip.ordinary_quarter_choice Q P b (g j) (hOrd j.val hj)
      exact ⟨i, fun _ ↦ ⟨hi, hq⟩⟩
    · exact ⟨0, fun h ↦ False.elim (hj h)⟩
  choose selected hselected using hs
  refine ⟨selected, ?_, ?_⟩
  · intro j hj
    let v : G := ⟨j, hJ hj⟩
    have hi := (hselected v hj).1
    rw [selectedPrime_apply D selected v (hactive hj)]
    exact PaperP1.NonanchorPivotSelection.pivot_le_of_ordinary hi
  · intro j hj
    exact (hselected ⟨j, hJ hj⟩ hj).2

end PaperP1.RandomizedHybridSourceSelection
