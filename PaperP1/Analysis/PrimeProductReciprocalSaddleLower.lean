module

public import PaperP1.Analysis.PrimeProductReciprocalLower
public import PaperP1.Analysis.PrimeProductSaddleChoice
public import PaperP1.Analysis.CoarseSaddlePowerErrors
public import PaperP1.Analysis.ElementaryPivotLogRate

/-! # An internal coarse saddle lower bound for ordinary and odd-pivot reciprocals

The coefficient ten is deliberately explicit and weaker than the fine EIP
coefficient two. No ordinary reciprocal-prime asymptotic is an input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeProductReciprocalSaddleLower

open Filter SaddleParameters SaddleScales HardSaddleGrowth ReciprocalOddPivots DyadicOddPivots

theorem uniform_ordinary_lower : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    (N : ℝ) * Real.exp (-10 * saddleCutoff 1 (Real.log N)) ≤ primeSum N := by
  obtain ⟨Y₀, _hY₀, hlower⟩ := PrimeProductReciprocalLower.exponential_lower
  obtain ⟨H₀, horder⟩ := PrimeProductSaddleChoice.exists_order Y₀
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, h⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop H₀))
  refine ⟨N₀, ?_⟩
  intro N hN
  obtain ⟨hH, k, hk, hfloor, hscale, hcost⟩ := horder (Real.log N) (h N (by omega))
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hroot : (N : ℝ) ^ (1 / (k : ℝ)) = Real.exp (Real.log N / k) := by
    rw [Real.rpow_def_of_pos hn]
    congr 1
    ring
  have hh := hlower N k (by omega) hk hH (by simpa only [hroot] using hfloor) (by simpa only [hroot] using hscale)
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hcost])) hn.le).trans hh

theorem uniform_full_lower : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    (N : ℝ) * Real.exp (-10 * saddleCutoff 1 (Real.log N)) ≤ pivotSum N := by
  obtain ⟨N₀, h⟩ := uniform_ordinary_lower
  exact ⟨N₀, fun N hN ↦ (h N hN).trans (primeSum_le_pivotSum N)⟩

theorem uniform_dyadic_lower : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    (N : ℝ) * Real.exp (-11 * saddleCutoff 1 (Real.log N)) ≤ dyadicSum N := by
  obtain ⟨NF, hf⟩ := uniform_full_lower
  obtain ⟨NK, hk⟩ := DyadicReciprocalScaleBounds.logarithmic_prefactor 1 (by norm_num)
  obtain ⟨NP, hp⟩ := CoarseSaddlePowerErrors.power_negligible 1 (1 / 2) 10 (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨HB, hb⟩ := square_band_eventually
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop HB))
  refine ⟨max NF (max NK (max NP NG)), ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hH, hV, hsq, _hsq⟩ := hb (Real.log N) (hg N (by omega))
  let V := saddleCutoff 1 (Real.log N)
  let K : ℝ := ((Nat.clog 2 N + 1 : ℕ) : ℝ)
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hν : saddleNu 1 (Real.log N) ≤ V := by
    change Real.log N / V ≤ V
    exact (div_le_iff₀ hV).mpr (by nlinarith only [hsq])
  have hpref : 2 * K ≤ Real.exp V := by
    have hh := hk N (by omega)
    simp only [one_mul] at hh
    exact hh.trans (Real.exp_le_exp.mpr hν)
  have hroot : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hs : (Nat.sqrt N : ℝ) ^ 2 ≤ (N : ℝ) ^ 1 := by
      simpa only [pow_one] using (show (Nat.sqrt N : ℝ) ^ 2 ≤ N by
        exact_mod_cast (Nat.le_sqrt'.mp (le_refl (Nat.sqrt N))))
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (HostRealPowers.le_rpow_div_of_pow_le (Nat.cast_nonneg (Nat.sqrt N)) hn.le (by decide : 0 < 2) hs)
  have hroot1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hsmall : 2 * ((Nat.sqrt N : ℝ) + 1) ≤ (N : ℝ) / 2 * Real.exp (-10 * V) := by
    have hh := hp N (by omega)
    rw [Real.rpow_one] at hh
    change (N : ℝ) ^ (1 / 2 : ℝ) ≤ (1 / 8) * N * Real.exp (-10 * V) at hh
    linarith only [hroot, hroot1, hh]
  have htarget : K * ((N : ℝ) * Real.exp (-11 * V)) ≤ (N : ℝ) / 2 * Real.exp (-10 * V) := by
    calc
      _ ≤ (Real.exp V / 2) * ((N : ℝ) * Real.exp (-11 * V)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hpref]) (by positivity)
      _ = (N : ℝ) / 2 * (Real.exp V * Real.exp (-11 * V)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hfinite : pivotSum N ≤ 2 * ((Nat.sqrt N : ℝ) + 1) + K * dyadicSum N := by
    simpa only [K, Nat.cast_add, Nat.cast_one] using full_dyadic_lower_transfer N (by omega)
  have hfull := hf N (by omega)
  change (N : ℝ) * Real.exp (-10 * V) ≤ pivotSum N at hfull
  have hKtarget : K * ((N : ℝ) * Real.exp (-11 * V)) ≤ K * dyadicSum N := by
    linarith only [htarget, hsmall, hfinite, hfull]
  exact (mul_le_mul_iff_right₀ hKpos).mp hKtarget

theorem ordinary_power_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, (N : ℝ) ^ (1 - ε) ≤ primeSum N := by
  obtain ⟨NO, ho⟩ := uniform_ordinary_lower
  obtain ⟨NP, hp⟩ := CoarseSaddlePowerErrors.power_negligible 1 (1 - ε) 10 1 (by linarith only [hε]) (by norm_num)
  refine ⟨2 + NO + NP, by omega, ?_⟩
  intro N hN
  have hh := hp N (by omega)
  simp only [one_mul, Real.rpow_one] at hh
  exact hh.trans (ho N (by omega))

theorem ordinary_log_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      |Real.log (primeSum N) - Real.log N| ≤ ε * Real.log N := by
  obtain ⟨N₀, hN₀, h⟩ := ordinary_power_lower ε hε
  exact ⟨N₀, hN₀, fun N hN ↦ ElementaryPivotLogRate.log_sandwich (by omega) (h N hN) (primeSum_le N)⟩

theorem ordinary_normalized_log_limit :
    Tendsto (fun N : ℕ ↦ Real.log (primeSum N) / Real.log N) atTop (nhds 1) :=
  ElementaryPivotLogRate.limit_of_log_bound primeSum ordinary_log_bound

end PaperP1.PrimeProductReciprocalSaddleLower
