module

public import PaperP1.Analysis.ExponentialSmoothLower
public import PaperP1.Analysis.SmoothSaddleLoss
public import PaperP1.Analysis.PrimeProductReciprocalSaddleLower

/-! # Every leading reciprocal lower coefficient above two, internally

The internal smooth-density induction gives N exp(-c V_N) below each actual
ordinary/full/dyadic reciprocal sum for every fixed c>2. This leading-scale
statement does not give the fine o(nu_N) error of the full EIP equivalent.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothReciprocalLeadingLower

open Filter SaddleParameters SaddleScales HardSaddleGrowth ReciprocalOddPivots DyadicOddPivots

theorem uniform_ordinary_lower (c : ℝ) (hc : 2 < c) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ≤ primeSum N := by
  have hcpos : 0 < c := by linarith only [hc]
  let a := 2 / c
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : a < 1 := by dsimp only [a]; exact (div_lt_one hcpos).mpr hc
  have hid : 1 / a = c / 2 := by dsimp only [a]; field_simp
  have hca : 1 + 1 / a < c := by linarith only [hid, hc]
  obtain ⟨b, hb, NS, hs⟩ := ExponentialSmoothLower.uniform_saddle_lower a ha ha1
  obtain ⟨H₀, hloss⟩ := SmoothSaddleLoss.eventual_loss_bound a b c ha hb hca
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hg⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop H₀))
  refine ⟨max NS NG, ?_⟩
  intro N hN
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hh := hloss (Real.log N) (hg N (by omega))
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hh])) hn).trans
    (hs N (by omega))

theorem uniform_full_lower (c : ℝ) (hc : 2 < c) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ≤ pivotSum N := by
  obtain ⟨N₀, h⟩ := uniform_ordinary_lower c hc
  exact ⟨N₀, fun N hN ↦ (h N hN).trans (primeSum_le_pivotSum N)⟩

theorem uniform_dyadic_lower (c : ℝ) (hc : 2 < c) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ≤ dyadicSum N := by
  let c₁ := (c + 2) / 2
  let g := c - c₁
  have hc₁ : 2 < c₁ := by dsimp only [c₁]; linarith only [hc]
  have hgpos : 0 < g := by dsimp only [g, c₁]; linarith only [hc]
  obtain ⟨NF, hf⟩ := uniform_full_lower c₁ hc₁
  obtain ⟨NK, hk⟩ := DyadicReciprocalScaleBounds.logarithmic_prefactor g hgpos
  obtain ⟨NP, hp⟩ := CoarseSaddlePowerErrors.power_negligible 1 (1 / 2) c₁ (1 / 8) (by norm_num) (by norm_num)
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
  have hpref : 2 * K ≤ Real.exp (g * V) := by
    have hh := hk N (by omega)
    exact hh.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hν hgpos.le))
  have hroot : (Nat.sqrt N : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hs : (Nat.sqrt N : ℝ) ^ 2 ≤ (N : ℝ) ^ 1 := by
      simpa only [pow_one] using (show (Nat.sqrt N : ℝ) ^ 2 ≤ N by
        exact_mod_cast (Nat.le_sqrt'.mp (le_refl (Nat.sqrt N))))
    simpa only [Nat.cast_one, Nat.cast_ofNat] using
      (HostRealPowers.le_rpow_div_of_pow_le (Nat.cast_nonneg (Nat.sqrt N)) hn.le (by decide : 0 < 2) hs)
  have hroot1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hsmall : 2 * ((Nat.sqrt N : ℝ) + 1) ≤ (N : ℝ) / 2 * Real.exp (-c₁ * V) := by
    have hh := hp N (by omega)
    rw [Real.rpow_one] at hh
    change (N : ℝ) ^ (1 / 2 : ℝ) ≤ (1 / 8) * N * Real.exp (-c₁ * V) at hh
    linarith only [hroot, hroot1, hh]
  have htarget : K * ((N : ℝ) * Real.exp (-c * V)) ≤ (N : ℝ) / 2 * Real.exp (-c₁ * V) := by
    calc
      _ ≤ (Real.exp (g * V) / 2) * ((N : ℝ) * Real.exp (-c * V)) :=
        mul_le_mul_of_nonneg_right (by linarith only [hpref]) (by positivity)
      _ = (N : ℝ) / 2 * (Real.exp (g * V) * Real.exp (-c * V)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; dsimp only [g]; ring
  have hfinite : pivotSum N ≤ 2 * ((Nat.sqrt N : ℝ) + 1) + K * dyadicSum N := by
    simpa only [K, Nat.cast_add, Nat.cast_one] using full_dyadic_lower_transfer N (by omega)
  have hfull := hf N (by omega)
  change (N : ℝ) * Real.exp (-c₁ * V) ≤ pivotSum N at hfull
  have hKtarget : K * ((N : ℝ) * Real.exp (-c * V)) ≤ K * dyadicSum N := by
    linarith only [htarget, hsmall, hfinite, hfull]
  exact (mul_le_mul_iff_right₀ hKpos).mp hKtarget

theorem uniform_original_lower (c : ℝ) (hc : 2 < c) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
    ((N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ≤ primeSum N) ∧
      ((N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ≤ pivotSum N) ∧
      ((N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ≤ dyadicSum N) := by
  obtain ⟨NO, ho⟩ := uniform_ordinary_lower c hc
  obtain ⟨ND, hd⟩ := uniform_dyadic_lower c hc
  refine ⟨max NO ND, ?_⟩
  intro N hN
  have hh := ho N (by omega)
  exact ⟨hh, hh.trans (primeSum_le_pivotSum N), hd N (by omega)⟩

end PaperP1.SmoothReciprocalLeadingLower
