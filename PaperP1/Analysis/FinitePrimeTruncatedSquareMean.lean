module

public import PaperP1.Analysis.FinitePrimeDirichletTruncation

/-! # Uniform actual frequency square means for finite-prime integer Dirichlet polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePrimeTruncatedSquareMean
open Finset Filter MeasureTheory PaperP1 SlowPrimeBandSieve RealPrimeEulerBound
  FinitePrimeDirichletTruncation
open scoped Classical

theorem square_error_budget (F G : ℝ → ℝ) (hF : Continuous F) (hG : Continuous G)
    (hFpos : ∀ t, 0 ≤ F t) (e T : ℝ) (hT : 0 < T)
    (herror : ∀ t, F t ≤ G t+e) :
    (∫ t in -T..T, (F t)^2) ≤ 2*(∫ t in -T..T, (G t)^2)+4*T*e^2 := by
  have hp (t : ℝ) : (F t)^2 ≤ 2*(G t)^2+2*e^2 := by
    have hh := pow_le_pow_left₀ (hFpos t) (herror t) 2
    nlinarith [sq_nonneg (G t-e)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -T ≤ T)
    ((hF.pow 2).intervalIntegrable (-T) T)
    (((continuous_const.mul (hG.pow 2)).add continuous_const).intervalIntegrable (-T) T)
    (fun t ht ↦ hp t)
  change (∫ t in -T..T, (F t)^2) ≤ ∫ t in -T..T, 2*(G t)^2+2*e^2 at hi
  have hGi : IntervalIntegrable (fun t : ℝ ↦ 2*(G t)^2) volume (-T) T :=
    (continuous_const.mul (hG.pow 2)).intervalIntegrable (-T) T
  rw [intervalIntegral.integral_add hGi
    intervalIntegrable_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  nlinarith

theorem normalized_truncated_square_mean_small (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : ℝ, upper N ≤ T → ∀ f : ℕ →* ℝ,
        (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
        (∫ t in -T..T, (Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N))*
          ‖truncated (primes N) N (fun n ↦ (f n : ℂ)) t‖)^2) ≤ η*T := by
  obtain ⟨N₁,hN₁,hmean⟩ := RealEulerSquareMean.normalized_square_mean_small (η/4) (by positivity)
  have he : Tendsto (fun N : ℕ ↦ 4*((N : ℝ)^(-(1/4 : ℝ)))^2) atTop (nhds 0) := by
    have hh := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).pow 2
    simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,Function.comp_def] using hh.const_mul 4
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (slow_band_uniform_truncation.and
    (he.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < η/2))))
  refine ⟨max 2 (max N₁ N₂),le_max_left _ _,?_⟩
  intro N hN T hT f hf
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hTpos : 0 < T := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).trans_le hT
  have hdata := hN₂ N (by omega)
  have ha : ∀ n ∈ Nat.factoredNumbers (primes N), ‖(f n : ℂ)‖ ≤ 1 := by
    intro n hn
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact real_hom_bound f hf n hn.1
  have herror (t : ℝ) : Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N))*
      ‖truncated (primes N) N (fun n ↦ (f n : ℂ)) t‖ ≤
      normalized (primes N) f t+(N : ℝ)^(-(1/4 : ℝ)) := by
    have herr := hdata.1 (fun n ↦ (f n : ℂ)) ha t
    have hn : ‖truncated (primes N) N (fun n ↦ (f n : ℂ)) t‖ ≤
        ‖total (primes N) (fun n ↦ (f n : ℂ)) t‖+
          ‖total (primes N) (fun n ↦ (f n : ℂ)) t-truncated (primes N) N (fun n ↦ (f n : ℂ)) t‖ := by
      simpa only [sub_sub_cancel] using norm_sub_le
        (total (primes N) (fun n ↦ (f n : ℂ)) t)
        (total (primes N) (fun n ↦ (f n : ℂ)) t-truncated (primes N) N (fun n ↦ (f n : ℂ)) t)
    have hmass : 0 ≤ PrimeAvoidanceSieve.reciprocalMass (primes N) := sum_nonneg (fun p hp ↦ by positivity)
    have hexp : Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N)) ≤ 1 :=
      (Real.exp_le_one_iff).mpr (by linarith)
    have hs := mul_le_mul_of_nonneg_left hn (Real.exp_pos (-PrimeAvoidanceSieve.reciprocalMass (primes N))).le
    have ht : Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N))*
        ‖total (primes N) (fun n ↦ (f n : ℂ)) t‖=normalized (primes N) f t := by
      have hv := FinitePrimeDirichletSeries.value_eq_product (primes N) (fun p hp ↦ (mem_filter.mp hp).2) f hf t
      change Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N))*‖FinitePrimeDirichletSeries.value (primes N) f t‖=_
      rw [hv]
      rfl
    rw [mul_add,ht] at hs
    have hb := mul_le_mul hexp herr (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hb' : Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N))*
        ‖total (primes N) (fun n ↦ (f n : ℂ)) t-truncated (primes N) N (fun n ↦ (f n : ℂ)) t‖ ≤
          (N : ℝ)^(-(1/4 : ℝ)) := by simpa only [one_mul] using hb
    exact hs.trans (add_le_add le_rfl hb')
  have hcF : Continuous (fun t ↦ Real.exp (-PrimeAvoidanceSieve.reciprocalMass (primes N))*
      ‖truncated (primes N) N (fun n ↦ (f n : ℂ)) t‖) :=
    continuous_const.mul (truncated_continuous _ _ _).norm
  have hb := square_error_budget _ _ hcF
    (normalized_continuous (primes N) (fun p hp ↦ (mem_filter.mp hp).2) f (fun p hp ↦ hf p (mem_filter.mp hp).2))
    (fun t ↦ by positivity)
    ((N : ℝ)^(-(1/4 : ℝ))) T hTpos herror
  have hm := hmean N (by omega) T hT f (fun p hp ↦ hf p (mem_filter.mp hp).2)
  have hs := hdata.2
  nlinarith
end FinitePrimeTruncatedSquareMean
