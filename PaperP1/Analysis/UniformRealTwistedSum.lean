module

public import PaperP1.Analysis.HalaszSmallBudget
public import PaperP1.Analysis.RealUnitTwist
public import PaperP1.Analysis.UniformRealEulerBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformRealTwistedSum
open Finset Filter PaperP1 LogarithmicPhase
open scoped Classical

theorem uniform_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ‖∑ n ∈ Icc 1 X, (f n : ℂ)*phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨η,hη,XH,hXH,hHalasz⟩ := HalaszSmallBudget.summatory_small_of_budget ε hε
  obtain ⟨T₀,hT₀,XE,hXE,hEuler⟩ := UniformRealEulerBudget.uniform_bound B η hB hη
  refine ⟨T₀,hT₀,max XH XE,by omega,?_⟩
  intro X hX f hf τ hLower hUpper
  have hBudget : GlobalTripleBand.budget X (RealUnitTwist.unitTwist f τ) ≤ η*(Real.log (X : ℝ))^2 := by
    unfold GlobalTripleBand.budget
    rw [RealUnitTwist.frequencyBudget_twist_eq X f hf τ]
    exact hEuler X (by omega) f hf τ hLower hUpper _
  have hh := hHalasz X (by omega) (RealUnitTwist.unitTwist f τ)
    (RealUnitTwist.unitTwist_prime_bound f hf τ) hBudget
  simpa only [RealUnitTwist.summatory_twist] using hh

theorem normalized_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ‖∑ n ∈ Icc 1 X, (f n : ℂ)*phase (-Real.log (n : ℝ)) τ‖/(X : ℝ) ≤ ε := by
  obtain ⟨T₀,hT₀,X₀,hX₀,hBound⟩ := uniform_bound B ε hB hε
  refine ⟨T₀,hT₀,X₀,hX₀,?_⟩
  intro X hX f hf τ hLower hUpper
  have hXP : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  exact (div_le_iff₀ hXP).mpr (hBound X hX f hf τ hLower hUpper)

theorem polynomial_band_bound (a B ε : ℝ) (ha : 0 < a) (hB : 0 < B) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ : ℝ, (X : ℝ)^a ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ‖∑ n ∈ Icc 1 X, (f n : ℂ)*phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨T₀,hT₀,X₁,hX₁,hBound⟩ := uniform_bound B ε hB hε
  have hPower := (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp (hPower.eventually (eventually_ge_atTop T₀))
  refine ⟨max X₁ X₂,by omega,?_⟩
  intro X hX f hf τ hLower hUpper
  exact hBound X (by omega) f hf τ ((hX₂ X (by omega)).trans hLower) hUpper
end PaperP1.UniformRealTwistedSum
