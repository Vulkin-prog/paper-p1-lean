module

public import PaperP1.Analysis.RealPrimeEulerBound

/-! # An actual exceptional-set square-integral budget with exact restricted measures -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExceptionalSquareIntegral
open MeasureTheory Set

theorem square_integral_budget (F : ℝ → ℝ) (hF : Continuous F) (T M δ : ℝ)
    (hT : 0 < T) (E : Set ℝ) (hE : MeasurableSet E)
    (hsub : E ⊆ Ioc (-T) T) (hnonneg : ∀ t ∈ Ioc (-T) T, 0 ≤ F t)
    (hbound : ∀ t ∈ Ioc (-T) T, F t ≤ M) (hoff : ∀ t ∈ Ioc (-T) T, t ∉ E → F t ≤ δ) :
    (∫ t in -T..T, (F t)^2) ≤ 2*T*δ^2+M^2*volume.real E := by
  let μ := volume.restrict (Ioc (-T) T)
  have : IsFiniteMeasure μ := ⟨by dsimp only [μ]; finiteness⟩
  have hFi : Integrable (fun t ↦ (F t)^2) μ := ((hF.pow 2).intervalIntegrable (-T) T).1
  have hGi : Integrable (fun t ↦ δ^2+E.indicator (fun _ ↦ M^2) t) μ :=
    (integrable_const _).add ((integrable_const _).indicator hE)
  have hp : ∀ᵐ t ∂μ, (F t)^2 ≤ δ^2+E.indicator (fun _ ↦ M^2) t := by
    change ∀ᵐ t ∂volume.restrict (Ioc (-T) T), _
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    apply Filter.Eventually.of_forall
    intro t ht
    by_cases he : t ∈ E
    · rw [Set.indicator_of_mem he]
      exact (pow_le_pow_left₀ (hnonneg t ht) (hbound t ht) 2).trans (le_add_of_nonneg_left (sq_nonneg δ))
    · rw [Set.indicator_of_notMem he,add_zero]
      exact pow_le_pow_left₀ (hnonneg t ht) (hoff t ht he) 2
  have hm := integral_mono_ae hFi hGi hp
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hE),
    integral_const,integral_indicator_const _ hE,smul_eq_mul,smul_eq_mul] at hm
  have hvol : μ.real Set.univ=2*T := by
    dsimp only [μ]
    rw [measureReal_restrict_apply_univ,Real.volume_real_Ioc_of_le (by linarith : -T ≤ T)]
    ring
  have hmeas : μ.real E=volume.real E := by
    dsimp only [μ]
    rw [measureReal_restrict_apply hE,Set.inter_eq_left.mpr hsub]
  rw [hvol,hmeas] at hm
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  change (∫ t : ℝ, (F t)^2 ∂μ) ≤ _
  nlinarith
end ExceptionalSquareIntegral
