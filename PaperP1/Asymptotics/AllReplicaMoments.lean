module

public import PaperP1.Asymptotics.ReplicaMomentTheorem
public import PaperP1.Asymptotics.EmptyReplicaMoment

/-! # All fixed positive moment orders and all fixed occurrence lengths -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllReplicaMoments

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.InfiniteReplicaPositiveSum

local instance allReplicaMomentsMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem all_lengths (r q : ℕ) (C D A₀ ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Y : ℕ, ∀ (κ : Type*) [Fintype κ], ∀ color : Fin r → κ, ∀ c : ℕ → Fin L → F₂,
      ∀ A : Finset (Fin r → ℕ), (∀ x ∈ A, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ w : (Fin r → ℕ) → ℝ, (∀ x ∈ A, 0 ≤ w x) →
      (∀ x ∈ A, w x ≤ D * (Real.log N) ^ A₀) →
        (∫ ω, (randomSum Y L color c A w ω) ^ (q + 1) ∂infiniteRademacherMeasure) ≤
          (N : ℝ) ^ ε * ∫ ω, randomSum Y L color c A w ω ∂infiniteRademacherMeasure := by
  cases r with
  | zero =>
    obtain ⟨N₀, hN₀⟩ := EmptyReplicaMoment.positive_moment q D A₀ ε hD hε
    refine ⟨N₀, ?_⟩
    intro N hN L _ Y κ _ color c A _ w hw hbound
    exact hN₀ N hN Y L κ color c A w hw hbound
  | succ r => exact ReplicaMomentTheorem.positive_moment (r + 1) (by omega) q C D A₀ ε hD hε

theorem companion_T22_7_moment (r n : ℕ) (hn : 1 ≤ n) (C D A₀ ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Y : ℕ, ∀ (κ : Type*) [Fintype κ], ∀ color : Fin r → κ, ∀ c : ℕ → Fin L → F₂,
      ∀ A : Finset (Fin r → ℕ), (∀ x ∈ A, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ w : (Fin r → ℕ) → ℝ, (∀ x ∈ A, 0 ≤ w x) →
      (∀ x ∈ A, w x ≤ D * (Real.log N) ^ A₀) →
        (∫ ω, (randomSum Y L color c A w ω) ^ n ∂infiniteRademacherMeasure) ≤
          (N : ℝ) ^ ε * ∫ ω, randomSum Y L color c A w ω ∂infiniteRademacherMeasure := by
  cases n with
  | zero => omega
  | succ q => exact all_lengths r q C D A₀ ε hD hε

end PaperP1.AllReplicaMoments
