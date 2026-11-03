module

public import PaperP1.Asymptotics.CriticalGridGraphExclusion

/-! # One critical threshold works for every rational-graph degree up to a fixed bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedDegreeGridGraphExclusion

theorem cutoff_lt_scale (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ d : ℕ, 0 < d → d ≤ E → GridRationalGraphExclusion.bound d B < N := by
  induction E with
  | zero =>
    refine ⟨0, ?_⟩
    intro N hN L B hcrit hB hBL d hd hde
    omega
  | succ E ih =>
    obtain ⟨N₁, hN₁⟩ := ih
    obtain ⟨N₂, hN₂⟩ := CriticalGridGraphExclusion.cutoff_lt_scale C (E + 1) J (by omega)
    refine ⟨max N₁ N₂, ?_⟩
    intro N hN L B hcrit hB hBL d hd hde
    by_cases h : d ≤ E
    · exact hN₁ N ((le_max_left _ _).trans hN) L B hcrit hB hBL d hd h
    · have heq : d = E + 1 := by omega
      subst d
      exact hN₂ N ((le_max_right _ _).trans hN) L B hcrit hB hBL

end PaperP1.BoundedDegreeGridGraphExclusion
