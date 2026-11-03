module

public import PaperP1.Arithmetic.TwoTargetDensePairs

/-! # The full literal source-excluding dense pair population, including weak alignment and every direct pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetAdmissibleDensePairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.TwoTargetDensePairs

local instance admissiblePairsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def Admissible (θ : ℝ) (y z L : ℕ) : Prop :=
  ¬ CompressedTargetAlignment.Aligned 1 y z L ∨
    (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) ≤ θ * L

theorem of_pair_direct {θ : ℝ} (hθ : 0 ≤ θ) {y z L : ℕ}
    (hdisj : Disjoint (squareClassSpace y L) (squareClassSpace z L)) : Admissible θ y z L := by
  apply Or.inr
  have hbot : squareClassSpace y L ⊓ squareClassSpace z L = ⊥ := disjoint_iff.mp hdisj
  change (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) ≤ θ * L
  rw [hbot, finrank_bot, Nat.cast_zero]
  exact mul_nonneg hθ (Nat.cast_nonneg L)

def pairs {s : ℕ} (x : Fin s → ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (N L : ℕ) (η θ : ℝ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N ×ˢ dyadicBlock N).filter fun p ↦ p.1 ≠ p.2 ∧
    (∀ i, p.1 ≠ x i ∧ p.2 ≠ x i) ∧ Admissible θ p.1 p.2 L ∧
    Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
    η * L ≤ (deficit W p.1 p.2 L : ℝ)

theorem mem_pairs {s : ℕ} (x : Fin s → ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (N L : ℕ)
    (η θ : ℝ) (p : ℕ × ℕ) :
    p ∈ pairs x W N L η θ ↔ p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧
      (∀ i, p.1 ≠ x i ∧ p.2 ≠ x i) ∧ Admissible θ p.1 p.2 L ∧
      Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
      η * L ≤ (deficit W p.1 p.2 L : ℝ) := by
  simp only [pairs, mem_filter, mem_product]
  exact and_assoc

end PaperP1.TwoTargetAdmissibleDensePairs
