module

public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Analysis.ActualEulerBand
public import PaperP1.Analysis.CommonFullEulerBudget
public import PaperP1.Analysis.GlobalTripleBand
public import PaperP1.Analysis.HalaszSmallBudget
public import PaperP1.Analysis.LogarithmicGaussianTail
public import PaperP1.Analysis.RealUnitTwist

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonRealTwistedSum
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem common_twisted_summatory_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ T : ℝ, 1 ≤ T →
      (ActualEulerBand.frequencyCutoff X : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖∑ n ∈ Icc 1 X, (f n : ℂ)*LogarithmicPhase.phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨η,hη,X₁,hX₁,hhalasz⟩ := HalaszSmallBudget.summatory_small_of_budget ε hε
  obtain ⟨X₂,hX₂,hbudget⟩ := CommonFullEulerBudget.common_budget_small_uniform η δ hη hδ
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₃,hX₃⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop 1))
  refine ⟨max (max X₁ X₂) (max X₃ 4),by omega,?_⟩
  intro X hX T hT hMT
  have hL : 1 ≤ Real.log (X : ℝ) := hX₃ X (by omega)
  have hcube : (SlowPrimeBandSieve.upper X)^3 ≤ T := by
    have hp := pow_le_pow_right₀ hL (by decide : (3 : ℕ) ≤ 10)
    have hc : LogarithmicGaussianTail.height X ≤ (ActualEulerBand.frequencyCutoff X : ℝ) := Nat.le_ceil _
    exact hp.trans (hc.trans hMT)
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hbudget X (by omega) (ActualEulerBand.frequencyCutoff X) T hT hMT hcube
  refine ⟨E,hE,hsub,hm,?_⟩
  intro f hf τ hτ hnot
  have hb := hoff X le_rfl f hf τ hτ hnot
  have hb' : GlobalTripleBand.budget X (RealUnitTwist.unitTwist f τ) ≤ η*(Real.log (X : ℝ))^2 := by
    rw [GlobalTripleBand.budget,RealUnitTwist.frequencyBudget_twist_eq X f hf τ]
    exact hb
  have hs := hhalasz X (by omega) (RealUnitTwist.unitTwist f τ) (RealUnitTwist.unitTwist_prime_bound f hf τ) hb'
  rw [RealUnitTwist.summatory_twist] at hs
  exact hs
end PaperP1.CommonRealTwistedSum
