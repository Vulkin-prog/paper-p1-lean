module

public import PaperP1.Analysis.MultiplicativeShortAverage
public import PaperP1.Arithmetic.OrdinarySmoothIndicator

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CompleteShortAverage
open Finset Nat MeasureTheory PaperP1 Filter MultiplicativeShortAverage
open scoped Classical

def MeanSquareInput (ψ : ℕ → ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      (∑ j ∈ Ico N (2*N), (shortMean f j (ψ N)-longMean f N)^2) ≤ δ*(N : ℝ)

def ConcentrationInput (ψ : ℕ → ℕ) : Prop :=
  ∀ ε τ : ℝ, 0 < ε → 0 < τ → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ((bad f N (ψ N) ε).card : ℝ) ≤ τ*(N : ℝ)

theorem concentration_of_mean_square (ψ : ℕ → ℕ) (hInput : MeanSquareInput ψ) : ConcentrationInput ψ := by
  intro ε τ hε hτ
  obtain ⟨N₀,hN₀⟩ := hInput (τ*ε^2) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN f hf
  have hm := hN₀ N hN f hf
  have hc := MultiplicativeShortAverage.finite_square_budget (Ico N (2*N))
    (fun j ↦ shortMean f j (ψ N)-longMean f N) ε hε.le
  change ((bad f N (ψ N) ε).card : ℝ)*ε^2 ≤ _ at hc
  have hs : 0 < ε^2 := sq_pos_of_pos hε
  nlinarith

def smoothHom (Y : ℕ) (hY : 1 ≤ Y) : ℕ →* ℝ where
  toFun := OrdinarySmoothIndicator.value Y
  map_one' := OrdinarySmoothIndicator.value_one Y hY
  map_mul' := OrdinarySmoothIndicator.value_mul Y

theorem smoothHom_bound (Y : ℕ) (hY : 1 ≤ Y) (n : ℕ) : |smoothHom Y hY n| ≤ 1 := by
  change |OrdinarySmoothIndicator.value Y n| ≤ 1
  rw [abs_of_nonneg (OrdinarySmoothIndicator.value_nonneg Y n)]
  exact OrdinarySmoothIndicator.value_le_one Y n

theorem smoothHom_prime_bound (Y : ℕ) (hY : 1 ≤ Y) : ∀ p : ℕ, p.Prime → |smoothHom Y hY p| ≤ 1 :=
  fun p _hp ↦ smoothHom_bound Y hY p
end PaperP1.CompleteShortAverage
