module

public import PaperP1.Analysis.ExceptionalSquareIntegral

/-! # Uniform small frequency mean square of actual normalized finite real Euler products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealEulerSquareMean
open Finset Filter MeasureTheory PaperP1 RealPrimeEulerBound SlowPrimeBandSieve
open scoped Classical

theorem normalized_square_mean_small (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : ℝ, upper N ≤ T → ∀ f : ℕ → ℝ,
        (∀ p ∈ primes N, |f p| ≤ 1) →
        (∫ t in -T..T, (normalized (primes N) f t)^2) ≤ η*T := by
  let δ : ℝ := Real.sqrt η/4
  let ε : ℝ := η/(4*(Real.exp 1)^2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨N₁,hN₁,hexc⟩ := slow_band_uniform_off_exception δ ε hδ hε
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (geometry_eventually.and
    (upper_tendsto.eventually (eventually_ge_atTop 2)))
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN T hT f hf
  obtain ⟨E,hE,hsub,hmeas,hoff⟩ := hexc N (by omega) T hT
  have hg := hN₂ N (by omega)
  have hTp : 0 < T := by linarith [hg.2]
  have hsum : (∑ p ∈ primes N, 1/(p : ℝ)^2) ≤ 1 :=
    (square_tail_bound N hg.1.1).trans ((div_le_one (by linarith [hg.1.1] : 0 < lower N)).mpr hg.1.1)
  have hglobal (t : ℝ) : normalized (primes N) f t ≤ Real.exp 1 :=
    (normalized_global_bound (primes N) (fun p hp ↦ (mem_filter.mp hp).2) f hf t).trans
      (Real.exp_le_exp.mpr hsum)
  have hb := ExceptionalSquareIntegral.square_integral_budget (normalized (primes N) f)
    (normalized_continuous (primes N) (fun p hp ↦ (mem_filter.mp hp).2) f hf) T (Real.exp 1) δ hTp
    E hE hsub (fun t ht ↦ normalized_nonneg _ _ _)
    (fun t ht ↦ hglobal t) (fun t ht hnot ↦ hoff t ht hnot f hf)
  have hsq : δ^2=η/16 := by dsimp only [δ]; rw [div_pow,Real.sq_sqrt hη.le]; norm_num
  have hcancel : (Real.exp 1)^2*ε=η/4 := by dsimp only [ε]; field_simp
  have hc : 2*T*δ^2+(Real.exp 1)^2*volume.real E ≤ η*T := by
    have hm := mul_le_mul_of_nonneg_left hmeas (sq_nonneg (Real.exp 1))
    rw [hsq] at *
    have he : (Real.exp 1)^2*(ε*T)=η/4*T := by rw [← mul_assoc,hcancel]
    rw [he] at hm
    nlinarith
  exact hb.trans hc
end RealEulerSquareMean
