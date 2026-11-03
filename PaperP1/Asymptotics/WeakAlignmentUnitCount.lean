module

public import PaperP1.Arithmetic.UnitIntersectionRankLower
public import PaperP1.Coding.LocalRigidityRegimes
public import PaperP1.Model.FiniteRademacher

/-! # The actual unit count on every channel is uniformly controlled by the effective target intersection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakAlignmentUnitCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount

local instance weakUnitCountPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem uniform_bound (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      ∀ a b : ℕ, 0 < a → 0 < b →
        (units a b y z L).card ≤ Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) + 2 := by
  obtain ⟨Nr, hr⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one (1 / 2) C (by norm_num)
  refine ⟨max 3 Nr, by omega, ?_⟩
  intro N hN L hband y z hy hz a b ha hb
  have hylo := (mem_Ico.mp hy).1
  have hzlo := (mem_Ico.mp hz).1
  have hbase : (1 / 2 : ℝ) * N ≤ ((y - 1 : ℕ) : ℝ) := by
    have h : (N : ℝ) ≤ 2 * ((y - 1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ 2 * (y - 1) by omega)
    linarith only [h]
  exact UnitIntersectionRankLower.unit_count_le_intersection_add_two ha hb (by omega) (by omega)
    (hr N (by omega) (y - 1) L hbase hband)

theorem uniform_weak_bound (C : ℝ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      ∀ θ : ℝ, (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) ≤ θ * L →
      ∀ a b : ℕ, 0 < a → 0 < b → ((units a b y z L).card : ℝ) ≤ θ * L + 2 := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_bound C
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband y z hy hz θ hweak a b ha hb
  have h : ((units a b y z L).card : ℝ) ≤
      (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) + 2 := by
    exact_mod_cast hu N hN L hband y z hy hz a b ha hb
  linarith only [h, hweak]

end PaperP1.WeakAlignmentUnitCount
