module

public import PaperP1.Analysis.CommonFullEulerBudget
public import PaperP1.Analysis.HalaszSmallBudget
public import PaperP1.Analysis.RealUnitTwist
public import PaperP1.Analysis.FrequencyBudgetMonotone

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.CommonUniformTwistedSum
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem common_uniform_summatory_small (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ B : ℕ, N ≤ B → ∀ T : ℝ, 1 ≤ T →
      (ActualEulerBand.frequencyCutoff B : ℝ) ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ δ*T ∧
        ∀ X : ℕ, N ≤ X → X ≤ B → ∀ f : ℕ →* ℝ,
          (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ ∈ Set.Ioc (-T) T, τ ∉ E →
          ‖∑ n ∈ Icc 1 X, (f n : ℂ)*LogarithmicPhase.phase (-Real.log (n : ℝ)) τ‖ ≤ ε*(X : ℝ) := by
  obtain ⟨η,hη,N₁,hN₁,hhalasz⟩ := HalaszSmallBudget.summatory_small_of_budget ε hε
  obtain ⟨N₂,hN₂,hbudget⟩ := CommonFullEulerBudget.common_budget_small_uniform η δ hη hδ
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N₃,hN₃⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop 1))
  refine ⟨max (max N₁ N₂) (max N₃ 4),by omega,?_⟩
  intro N hN B hNB T hT hcut
  have hN4 : 4 ≤ N := by omega
  have hL : 1 ≤ Real.log (N : ℝ) := hN₃ N (by omega)
  have hKM := FrequencyBudgetMonotone.cutoff_mono N B (by omega) hNB
  have hKMR : (ActualEulerBand.frequencyCutoff N : ℝ) ≤ ActualEulerBand.frequencyCutoff B := by exact_mod_cast hKM
  have hcube : (SlowPrimeBandSieve.upper N)^3 ≤ T := by
    have hp := pow_le_pow_right₀ hL (by decide : (3 : ℕ) ≤ 10)
    have hc : LogarithmicGaussianTail.height N ≤ (ActualEulerBand.frequencyCutoff N : ℝ) := Nat.le_ceil _
    exact hp.trans (hc.trans (hKMR.trans hcut))
  obtain ⟨E,hE,hsub,hm,hoff⟩ := hbudget N (by omega) (ActualEulerBand.frequencyCutoff B) T hT hcut hcube
  refine ⟨E,hE,hsub,hm,?_⟩
  intro X hNX hXB f hf τ hτ hnot
  have hX2 : 2 ≤ X := by omega
  have hXKM := FrequencyBudgetMonotone.cutoff_mono X B hX2 hXB
  let F := fun t : ℝ ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)
  have hF : Continuous F :=
    (RealPrimeEulerBound.product_continuous (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X) f
      (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp))).comp (continuous_id.add_const τ)
  have hmono := FrequencyBudgetMonotone.frequencyBudget_mono F hF
    (ActualEulerBand.frequencyCutoff X) (ActualEulerBand.frequencyCutoff B) hXKM
  have hsmall := hoff X hNX f hf τ hτ hnot
  have hb : GlobalTripleBand.budget X (RealUnitTwist.unitTwist f τ) ≤ η*(Real.log (X : ℝ))^2 := by
    rw [GlobalTripleBand.budget,RealUnitTwist.frequencyBudget_twist_eq X f hf τ]
    exact hmono.trans hsmall
  have hs := hhalasz X (by omega) (RealUnitTwist.unitTwist f τ) (RealUnitTwist.unitTwist_prime_bound f hf τ) hb
  rw [RealUnitTwist.summatory_twist] at hs
  exact hs
end PaperP1.CommonUniformTwistedSum
