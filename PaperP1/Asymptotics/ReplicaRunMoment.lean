module

public import PaperP1.Asymptotics.AllReplicaMoments
public import PaperP1.Model.RunReplicaSums
public import PaperP1.Asymptotics.LargeBoundaryTail

/-! # Full T22.7 positive moment conclusion for the original run-start conditional probabilities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaRunMoment

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteRademacher

local instance replicaRunMomentMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem companion_T22_7 (r n : ℕ) (hn : 1 ≤ n) (C D A₀ ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Y : ℕ, ∀ (κ : Type*) [Fintype κ], ∀ color : Fin r → κ,
      ∀ A : Finset (Fin r → ℕ), (∀ x ∈ A, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ w : (Fin r → ℕ) → ℝ, (∀ x ∈ A, 0 ≤ w x) →
      (∀ x ∈ A, w x ≤ D * (Real.log N) ^ A₀) →
        (∫ ω, (RunReplicaSums.randomSum Y L color A w ω) ^ n ∂infiniteRademacherMeasure) ≤
          (N : ℝ) ^ ε * ∫ ω, RunReplicaSums.randomSum Y L color A w ω ∂infiniteRademacherMeasure := by
  obtain ⟨NM, hNM⟩ := AllReplicaMoments.companion_T22_7_moment r n hn C D A₀ ε hD hε
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  refine ⟨max NM NL, ?_⟩
  intro N hN L hband Y κ _ color A hA w hw hbound
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  have h := hNM N (by omega) L hband Y κ color (fun _ ↦ startRhs L) A hA w hw hbound
  simpa only [RunReplicaSums.sum_eq Y L hL color A w] using h

end PaperP1.ReplicaRunMoment
