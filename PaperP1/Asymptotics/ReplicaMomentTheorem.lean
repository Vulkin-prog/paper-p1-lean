module

public import PaperP1.Asymptotics.ReplicaFiniteMoment
public import PaperP1.Model.InfiniteReplicaPositiveSum

/-! # The positive weighted replica moment bound on the actual infinite prime-sign model -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaMomentTheorem

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.InfiniteReplicaPositiveSum

local instance replicaMomentTheoremMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem positive_moment (r : ℕ) (hr : 0 < r) (q : ℕ) (C D A₀ ε : ℝ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Y : ℕ, ∀ (κ : Type*) [Fintype κ], ∀ color : Fin r → κ, ∀ c : ℕ → Fin L → F₂,
      ∀ A : Finset (Fin r → ℕ), (∀ x ∈ A, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ w : (Fin r → ℕ) → ℝ, (∀ x ∈ A, 0 ≤ w x) →
      (∀ x ∈ A, w x ≤ D * (Real.log N) ^ A₀) →
        (∫ ω, (randomSum Y L color c A w ω) ^ (q + 1) ∂infiniteRademacherMeasure) ≤
          (N : ℝ) ^ ε * ∫ ω, randomSum Y L color c A w ω ∂infiniteRademacherMeasure := by
  obtain ⟨N₀, hN₀⟩ := ReplicaFiniteMoment.logarithmic_weight_moment r hr q C D A₀ ε hD hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband Y κ _ color c A hA w hw hbound
  let M := max Y (2 * N + L)
  have hYM : Y ≤ M := le_max_left _ _
  have hM : 2 * N + L ≤ M := le_max_right _ _
  have hcut : ∀ x ∈ A, ∀ i, x i + L ≤ M := by
    intro x hx i
    have hi := (mem_Ico.mp (hA x hx i)).2
    omega
  rw [moment_transport hYM color c A w hcut (q + 1), first_moment_transport hYM color c A w hcut]
  exact hN₀ N hN L hband κ M Y hM color c A hA w hw hbound

end PaperP1.ReplicaMomentTheorem
