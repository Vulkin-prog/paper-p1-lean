module

public import PaperP1.Asymptotics.AllCardinalityConnected
public import PaperP1.Asymptotics.AllCardinalityConnectedJoint

/-! # The stronger all-cardinality joint-plus-absolute-centered version of companion T16.1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllCardinalityTotalActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (η u C ε : ℝ) (hη : 0 ≤ η) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) ≤
          (N : ℝ) ^ (-min 1 (2 - η) + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := AllCardinalityConnected.uniform_bound
    η u C (ε / 2) hη hu (by positivity)
  obtain ⟨NJ, _hNJ, hj⟩ := AllCardinalityConnectedJoint.uniform_bound
    η u C (ε / 2) hη hu (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-min 1 (2 - η) + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NA + NJ + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  calc
    _ = (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) +
        ∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I| := by
      simp_rw [mul_add]
      rw [sum_add_distrib]
    _ ≤ (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) + (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) :=
      add_le_add (hj N (by omega) L hband G hG F hF) (ha N (by omega) L hband G hG F hF)
    _ = 2 * (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-min 1 (2 - η) + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.AllCardinalityTotalActivity
