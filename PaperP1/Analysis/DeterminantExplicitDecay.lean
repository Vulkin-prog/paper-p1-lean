module

public import PaperP1.Analysis.WeightedLatticeCost

/-! # The sharp weighted monomial decay with a fully explicit linear error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantExplicitDecay

open Finset PaperP1.DeterminantIntegerRows PaperP1.WeightedLatticeTriangle
  PaperP1.DeterminantChartBound

def lowerCost (H : ℕ) (r₁ r₂ : ℝ) : ℝ :=
  (2 / 3 : ℝ) * H * Real.sqrt (2 * r₁ * r₂ * H) - (r₁ + r₂) * H

theorem injective_cost_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ × ℕ) (hf : Function.Injective f) (r₁ r₂ : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    lowerCost (Fintype.card ι) r₁ r₂ ≤ ∑ i, cost r₁ r₂ (f i) := by
  have h := WeightedLatticeCost.finite_set_cost_lower (univ.image f) r₁ r₂ hr₁ hr₂
  rw [card_image_of_injective _ hf, card_univ, sum_image (fun i _ j _ hij ↦ hf hij)] at h
  exact h

theorem exponent_cost_lower (A B : ℕ) (f : Exponent A B → Exponent (A + 2 * B) B)
    (hf : Function.Injective f) (r₁ r₂ : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    lowerCost ((A + 1) * (B + 1)) r₁ r₂ ≤
      ∑ i, (r₁ * (f i).1.val + r₂ * (f i).2.val) := by
  have hval : Function.Injective (fun k : Exponent (A + 2 * B) B ↦ (k.1.val, k.2.val)) := by
    intro p q hpq
    exact Prod.ext (Fin.ext (congrArg Prod.fst hpq)) (Fin.ext (congrArg Prod.snd hpq))
  have h := injective_cost_lower (fun i ↦ ((f i).1.val, (f i).2.val)) (hval.comp hf) r₁ r₂ hr₁ hr₂
  simpa only [Exponent, Fintype.card_prod, Fintype.card_fin, cost] using h

theorem normalized_explicit_bound (A B : ℕ) (α β : Exponent A B → ℝ) (r₁ r₂ : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hα : ∀ i, |α i| ≤ Real.exp (-r₁)) (hβ : ∀ i, |β i| ≤ Real.exp (-r₂)) :
    |(normalizedMatrix A B α β).det| ≤
      constant A B * Real.exp (-lowerCost ((A + 1) * (B + 1)) r₁ r₂) := by
  exact normalized_bound A B α β r₁ r₂ _ hα hβ
    (fun f hf ↦ exponent_cost_lower A B f hf r₁ r₂ hr₁ hr₂)

theorem original_explicit_bound (A B : ℕ) (s t α β : Exponent A B → ℝ) (s₀ t₀ r₁ r₂ : ℝ)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hs : ∀ i, s i = s₀ * (1 + α i))
    (ht : ∀ i, t i = t₀ * (1 + 2 * α i + α i ^ 2 + β i))
    (hα : ∀ i, |α i| ≤ Real.exp (-r₁)) (hβ : ∀ i, |β i| ≤ Real.exp (-r₂)) :
    |(Matrix.of (fun i j : Exponent A B ↦ s i ^ j.1.val * t i ^ j.2.val)).det| ≤
      |∏ j : Exponent A B, s₀ ^ j.1.val * t₀ ^ j.2.val| * constant A B *
        Real.exp (-lowerCost ((A + 1) * (B + 1)) r₁ r₂) := by
  exact original_bound A B s t α β s₀ t₀ r₁ r₂ _ hs ht hα hβ
    (fun f hf ↦ exponent_cost_lower A B f hf r₁ r₂ hr₁ hr₂)

theorem constant_positive (A B : ℕ) : 0 < constant A B := by
  unfold constant
  have hF : (0 : ℝ) < (((A + 1) * (B + 1)).factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos ((A + 1) * (B + 1))
  positivity

end PaperP1.DeterminantExplicitDecay
