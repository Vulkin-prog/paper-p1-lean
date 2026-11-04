module

public import PaperP1.Probability.IndependentFiniteProbability
public import PaperP1.Probability.WordForcingFlipCost
public import PaperP1.Arithmetic.NonanchorPivotSelection

/-! # A quarter-flip candidate for every randomized source orientation

The source word is uniform and the auxiliary law is arbitrary and
independent. The local lower-cost selection needs no fairness of the
orientation; fairness is a separate requirement for the Palm law.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedSourceFlip

open Finset PaperP1.Arithmetic PaperP1.Probability PaperP1.Algebra PaperP1.UniformFubini
  PaperP1.IndependentFiniteProbability PaperP1.BinaryForcingFlip

variable {ι Ξ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ξ]

def flip (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (i : ι) (p : (ι → F₂) × Ξ) : F₂ :=
  p.1 i + b i + g p.1 p.2

def probability (P : FiniteProbability Ξ) (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂) (i : ι) : ℝ :=
  finiteExpectation (product (uniformFiniteProbability (ι → F₂)) P).weight
    (fun p ↦ bitIndicator (flip b g i p))

theorem source_parity_fair (P : FiniteProbability Ξ) (b : ι → F₂) (i j : ι) (hji : j ≠ i) :
    finiteExpectation (product (uniformFiniteProbability (ι → F₂)) P).weight
      (fun p ↦ bitIndicator (p.1 i + p.1 j + b i + b j)) = (1 / 2 : ℝ) := by
  rw [expectation_product]
  simp only [finiteExpectation_const, P.total_weight, one_mul]
  simpa only [add_assoc] using uniform_parity_fair i j hji (b i + b j)

theorem quarter_choice (P : FiniteProbability Ξ) (b : ι → F₂) (g : (ι → F₂) → Ξ → F₂)
    (i j : ι) (hji : j ≠ i) :
    (1 / 4 : ℝ) ≤ probability P b g i ∨ (1 / 4 : ℝ) ≤ probability P b g j :=
  one_candidate_quarter (product (uniformFiniteProbability (ι → F₂)) P)
    (fun p ↦ p.1 i) (fun p ↦ p.1 j) (fun p ↦ g p.1 p.2) (b i) (b j)
    (source_parity_fair P b i j hji)

omit [Fintype ι] [DecidableEq ι] in
theorem correction_eq (u b s : F₂) : (b + s) - u = u + b + s := by
  revert u b s
  decide

theorem ordinary_quarter_choice {j B : ℕ} (Q : ℝ)
    (P : FiniteProbability Ξ) (b : Fin B → F₂) (g : (Fin B → F₂) → Ξ → F₂)
    (h : 2 ≤ (PaperP1.NonanchorPivotSelection.ordinaryIndices j B Q).card) :
    ∃ i : Fin B, i ∈ PaperP1.NonanchorPivotSelection.ordinaryIndices j B Q ∧
      (1 / 4 : ℝ) ≤ probability P b g i := by
  obtain ⟨i, hi⟩ := card_pos.mp (by omega : 0 < (PaperP1.NonanchorPivotSelection.ordinaryIndices j B Q).card)
  obtain ⟨k, hk, hki⟩ := Finset.exists_mem_ne (by omega : 1 <
    (PaperP1.NonanchorPivotSelection.ordinaryIndices j B Q).card) i
  rcases quarter_choice P b g i k hki with hq | hq
  · exact ⟨i, hi, hq⟩
  · exact ⟨k, hk, hq⟩

end PaperP1.RandomizedSourceFlip
