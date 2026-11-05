module

public import PaperP1.Analysis.ExponentialIntegralPowerLog
public import PaperP1.Analysis.BalancedReciprocalSaddleCost

/-! # Uniform fine counts over a moving logarithmic pivot range

The threshold precedes every cutoff v between twice the actual saddle
parameter and the logarithmic height. No reciprocal-prime input is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FineSaddlePivotCount

open Filter SaddleParameters SaddleScales SaddleAsymptotics BalancedReciprocalSaddleCost
  ExponentialIntegral OddPrimePivot

theorem uniform_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ v : ℝ,
      2 * saddleParameter 1 (Real.log N) ≤ v → v ≤ Real.log N →
        ((pivotValues (3 * N) ⌊Real.exp v⌋₊).card : ℝ) ≤
          3 * N * Real.exp (-Real.log N * saddleParameter 1 (Real.log N) / v +
            exponentialIntegral (saddleParameter 1 (Real.log N)) + ε * saddleNu 1 (Real.log N)) := by
  let η := ε / 4
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨C, _hC, heuler⟩ := ExponentialIntegralPowerLog.uniform_pivot_count η hη
  let A := (1 + η) * Real.exp 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have htail : Tendsto (fun H : ℝ ↦ (C + A * Real.log H) / saddleNu 1 H)
      atTop (nhds 0) := by
    have hc := (tendsto_const_nhds (x := C)).div_atTop
      (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1))
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      hc.add ((tendsto_log_div_saddleNu (by norm_num : (0 : ℝ) < 1)).const_mul A)
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (saddleThreshold 1)).and
      (((tendsto_saddleParameter_atTop (by norm_num : (0 : ℝ) < 1)).eventually
        (eventually_ge_atTop (1 : ℝ))).and
        ((tendsto_ei_div_nu.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))).and
          (htail.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2))))))
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlogT.eventually (eventually_ge_atTop H₀))
  refine ⟨N₀, ?_⟩
  intro N hN v hv hheight
  let H := Real.log (N : ℝ)
  let u := saddleParameter 1 H
  let ν := saddleNu 1 H
  let E := exponentialIntegral u
  let δ := u / v
  let σ := 1 - δ
  obtain ⟨hroot, hu1, hEi, herror⟩ := hH₀ H (hN₀ N (by omega))
  have hH : 0 < H := (saddleThreshold_pos (by norm_num : (0 : ℝ) < 1)).trans_le hroot
  have hV := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  have hν : 0 < ν := div_pos hH hV
  have hu : 0 < u := by change 1 ≤ u at hu1; linarith only [hu1]
  have hvp : 0 < v := by change 2 * u ≤ v at hv; linarith only [hu, hv]
  have hδ : 0 < δ := div_pos hu hvp
  have hδhalf : δ ≤ 1 / 2 := (div_le_iff₀ hvp).mpr (by change 2 * u ≤ v at hv; linarith only [hv])
  have hσ1 : σ ≤ 1 := by dsimp only [σ]; linarith only [hδ]
  have hR : 2 ≤ Real.exp v := by
    have hh := Real.add_one_le_exp v
    change 2 * u ≤ v at hv
    change 1 ≤ u at hu1
    linarith only [hh, hu1, hv]
  have harg : δ * Real.log (Real.exp v) = u := by
    rw [Real.log_exp]
    dsimp only [δ]
    field_simp
  have hlog : Real.log (1 / δ) ≤ Real.log H := by
    apply Real.log_le_log (by positivity : 0 < 1 / δ)
    have hid : 1 / δ = v / u := by dsimp only [δ]; field_simp
    rw [hid]
    apply (div_le_iff₀ hu).mpr
    change v ≤ H at hheight
    change 1 ≤ u at hu1
    nlinarith only [hheight, hu1, hH]
  have hE : E ≤ 2 * ν := (div_le_iff₀ hν).mp hEi.le
  have herr : C + A * Real.log H ≤ (ε / 2) * ν := (div_le_iff₀ hν).mp herror.le
  have hexponent : C + (1 + η) * E + A * Real.log (1 / δ) ≤ E + ε * ν := by
    have hl := mul_le_mul_of_nonneg_left hlog hA
    have he := mul_le_mul_of_nonneg_left hE hη.le
    dsimp only [η] at he ⊢
    nlinarith only [hl, he, herr]
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNpow : (N : ℝ) ^ σ = N * Real.exp (-H * u / v) := by
    rw [Real.rpow_def_of_pos hn]
    have hid : H * σ = H + -H * u / v := by dsimp only [σ, δ]; ring
    change Real.exp (H * σ) = _
    rw [hid, Real.exp_add, Real.exp_log hn]
  have hthree : ((3 * N : ℕ) : ℝ) ^ σ ≤ 3 * (N : ℝ) ^ σ := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hn.le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 3) hσ1) (Real.rpow_nonneg hn.le _)
  have hc := heuler (3 * N) δ (Real.exp v) hδ hδhalf hR
  rw [harg] at hc
  calc
    _ ≤ ((3 * N : ℕ) : ℝ) ^ σ * Real.exp (C + (1 + η) * E + A * Real.log (1 / δ)) := hc
    _ ≤ (3 * (N : ℝ) ^ σ) * Real.exp (E + ε * ν) :=
      mul_le_mul hthree (Real.exp_le_exp.mpr hexponent) (Real.exp_nonneg _) (by positivity)
    _ = 3 * N * Real.exp (-H * u / v + E + ε * ν) := by
      rw [hNpow]
      rw [show 3 * ((N : ℝ) * Real.exp (-H * u / v)) * Real.exp (E + ε * ν) =
        3 * N * (Real.exp (-H * u / v) * Real.exp (E + ε * ν)) by ring, ← Real.exp_add]
      congr 2
      ring

theorem uniform_population_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ v : ℝ,
      2 * saddleParameter 1 (Real.log N) ≤ v → v ≤ Real.log N →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 (3 * N) →
        (∀ n ∈ S, (largestOddPrime n : ℝ) ≤ Real.exp v) →
        (S.card : ℝ) ≤ 3 * N * Real.exp (-Real.log N * saddleParameter 1 (Real.log N) / v +
          exponentialIntegral (saddleParameter 1 (Real.log N)) + ε * saddleNu 1 (Real.log N)) := by
  obtain ⟨N₀, h⟩ := uniform_count ε hε
  refine ⟨N₀, ?_⟩
  intro N hN v hv hh S hS hcut
  have hsub : S ⊆ pivotValues (3 * N) ⌊Real.exp v⌋₊ := by
    intro n hn
    exact Finset.mem_filter.mpr ⟨hS hn, (Nat.le_floor_iff (Real.exp_nonneg v)).mpr (hcut n hn)⟩
  have hc : (S.card : ℝ) ≤ ((pivotValues (3 * N) ⌊Real.exp v⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (h N hN v hv hh)

end PaperP1.FineSaddlePivotCount
