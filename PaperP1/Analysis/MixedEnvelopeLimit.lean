module

public import PaperP1.Analysis.BoundedAmplificationFactor
public import PaperP1.Asymptotics.SlowPrimeBandSieve
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.MixedEnvelopeLimit
open Filter PaperP1

def envelope (N : ℕ) : ℝ :=
  32*BoundedAmplificationFactor.constant*(SlowPrimeBandSieve.lower N)^16*
    Real.exp (-((SlowPrimeBandSieve.lower N)^2)/100)

theorem envelope_nonneg (N : ℕ) : 0 ≤ envelope N := by
  unfold envelope
  have hh := BoundedAmplificationFactor.constant_pos
  positivity

theorem envelope_tendsto : Tendsto envelope atTop (nhds 0) := by
  have hsq : Tendsto (fun N : ℕ ↦ (SlowPrimeBandSieve.lower N)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp SlowPrimeBandSieve.lower_tendsto
  have hy := Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 100) hsq
  have hb := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).comp hy
  have hh : Tendsto (fun N : ℕ ↦ (32*BoundedAmplificationFactor.constant*(100 : ℝ)^8)*
      (((SlowPrimeBandSieve.lower N)^2/100)^8*Real.exp (-((SlowPrimeBandSieve.lower N)^2/100)))) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero] using hb.const_mul (32*BoundedAmplificationFactor.constant*(100 : ℝ)^8)
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun N ↦ by
    dsimp only [envelope]
    rw [show -((SlowPrimeBandSieve.lower N)^2/100)=-((SlowPrimeBandSieve.lower N)^2)/100 by ring]
    ring)

theorem small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, envelope N ≤ ε := by
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (envelope_tendsto.eventually (eventually_lt_nhds hε))
  exact ⟨max 1 N₁,le_max_left _ _,fun N hN ↦ (hN₁ N (by omega)).le⟩
end PaperP1.MixedEnvelopeLimit
