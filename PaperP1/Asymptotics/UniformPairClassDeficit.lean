module

public import PaperP1.Model.AllPairExtensionDeficit
public import PaperP1.Asymptotics.UniformIndependentDeficit

/-! # Any actual pair class contributes its absolute activity times the uniform independent deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformPairClassDeficit

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedPairExtensions PaperP1.AllPairExtensionDeficit

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ P : Finset (Finset ℕ), P ⊆ G.powersetCard 2 →
      classMass G L u P ≤ (N : ℝ) ^ (-1 / 2 + ε) * CompatibleActivitySplit.absolute L P := by
  obtain ⟨N₀, hN₀, h⟩ := UniformIndependentDeficit.uniform_bound 2 u C ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG P hP
  apply class_cap
  intro e he
  obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp (hP he)
  have heN : e ⊆ dyadicBlock N := hesub.trans hG
  exact h N hN L hband G hG e heN hecard.le (sourceSpace e L)
    (IntersectionExceptional.span_le_raw e L (fun x hx ↦ by
      have h := (mem_Ico.mp (heN hx)).1
      omega))

end PaperP1.UniformPairClassDeficit
