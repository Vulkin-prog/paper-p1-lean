module

public import PaperP1.Arithmetic.TwoTargetRegularization
public import PaperP1.Arithmetic.CompressedTargetAlignment
public import PaperP1.Model.FiniteRademacher

/-! # The literal source-excluding nonaligned dense pair population and printed effective deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetDensePairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.TwoTargetWindowSections

local instance densePairsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance propDecidable (P : Prop) : Decidable P := Classical.propDecidable P
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance kernelAddCommGroup {y z L : ℕ} (W : Submodule F₂ (ℕ →₀ F₂)) :
    AddCommGroup (Kernel y z L W) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := W × squareClassSpace y L × squareClassSpace z L) (Kernel y z L W)

def deficit (W : Submodule F₂ (ℕ →₀ F₂)) (y z L : ℕ) : ℕ :=
  Module.finrank F₂ W + Module.finrank F₂ (squareClassSpace y L) + Module.finrank F₂ (squareClassSpace z L) -
    Module.finrank F₂ (W ⊔ (squareClassSpace y L ⊔ squareClassSpace z L) : Submodule F₂ (ℕ →₀ F₂))

theorem deficit_eq_kernel {s : ℕ} (x : Fin s → ℕ) (L : ℕ) (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ⨆ i, squareClassSpace (x i) L) (y z : ℕ) :
    deficit W y z L = Module.finrank F₂ (Kernel y z L W) :=
  (TwoTargetRegularization.effective_dimension_formula x y z L W hW).symm

def pairs {s : ℕ} (x : Fin s → ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (N L : ℕ) (η : ℝ) : Finset (ℕ × ℕ) :=
  (dyadicBlock N ×ˢ dyadicBlock N).filter fun p ↦ p.1 ≠ p.2 ∧
    (∀ i, p.1 ≠ x i ∧ p.2 ≠ x i) ∧ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
    Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
    η * L ≤ (deficit W p.1 p.2 L : ℝ)

theorem mem_pairs {s : ℕ} (x : Fin s → ℕ) (W : Submodule F₂ (ℕ →₀ F₂)) (N L : ℕ) (η : ℝ) (p : ℕ × ℕ) :
    p ∈ pairs x W N L η ↔ p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N ∧ p.1 ≠ p.2 ∧
      (∀ i, p.1 ≠ x i ∧ p.2 ≠ x i) ∧ ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L ∧
      Disjoint W (squareClassSpace p.1 L) ∧ Disjoint W (squareClassSpace p.2 L) ∧
      η * L ≤ (deficit W p.1 p.2 L : ℝ) := by
  simp only [pairs, mem_filter, mem_product]
  exact and_assoc

end PaperP1.TwoTargetDensePairs
