module

public import PaperP1.Asymptotics.OrdinaryShortIntervalCensusInput
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-! # Exact finite square-budget concentration for independent multiplicative short-average inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiplicativeShortAverage
open Finset
open scoped Classical

def longMean (f : ℕ → ℝ) (N : ℕ) : ℝ := (∑ n ∈ Ico N (2*N), f n) / N

def shortMean (f : ℕ → ℝ) (j h : ℕ) : ℝ := (∑ r ∈ range h, f (j+r)) / h

def bad (f : ℕ → ℝ) (N h : ℕ) (ε : ℝ) : Finset ℕ :=
  (Ico N (2*N)).filter fun j ↦ ε < |shortMean f j h - longMean f N|

def MeanSquareInput (ψ : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ f : ArithmeticFunction ℝ, f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
      (∑ j ∈ Ico N (2*N), (shortMean f j (ψ N) - longMean f N)^2) ≤ δ * N

def ConcentrationInput (ψ : ℕ → ℕ) : Prop :=
  ∀ ε τ : ℝ, 0 < ε → 0 < τ → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ f : ArithmeticFunction ℝ, f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
      ((bad f N (ψ N) ε).card : ℝ) ≤ τ * N

theorem finite_square_budget {α : Type*} (S : Finset α) (g : α → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    ((S.filter fun j ↦ ε < |g j|).card : ℝ) * ε^2 ≤ ∑ j ∈ S, g j ^ 2 := by
  calc
    _ = ∑ _j ∈ S.filter (fun j ↦ ε < |g j|), ε^2 := by simp
    _ ≤ ∑ j ∈ S.filter (fun j ↦ ε < |g j|), g j ^ 2 := by
      apply sum_le_sum
      intro j hj
      have hh := (mem_filter.mp hj).2
      nlinarith [sq_abs (g j)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)

theorem concentration_of_mean_square (ψ : ℕ → ℕ) (hInput : MeanSquareInput ψ) : ConcentrationInput ψ := by
  intro ε τ hε hτ
  obtain ⟨N₀, hN₀⟩ := hInput (τ * ε^2) (by positivity)
  refine ⟨N₀, ?_⟩
  intro N hN f hf hbound
  have hm := hN₀ N hN f hf hbound
  have hc := finite_square_budget (Ico N (2*N))
    (fun j ↦ shortMean f j (ψ N) - longMean f N) ε hε.le
  change ((bad f N (ψ N) ε).card : ℝ) * ε^2 ≤ _ at hc
  have hs : 0 < ε^2 := sq_pos_of_pos hε
  nlinarith
end MultiplicativeShortAverage
