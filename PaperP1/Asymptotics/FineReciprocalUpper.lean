module

public import PaperP1.Asymptotics.FineSaddlePivotCount
public import PaperP1.Analysis.MovingLogarithmicPivotMass
public import PaperP1.Analysis.SaddleLogPrefactors
public import PaperP1.Analysis.CoarseSaddlePowerErrors
public import PaperP1.Arithmetic.DyadicOddPivots

/-! # Fine one-sided reciprocal pivot estimates

A growing logarithmic partition uses a single actual saddle parameter.
All counting and cost premises are supplied by internal proofs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FineReciprocalUpper

open Finset Filter SaddleParameters SaddleScales SaddleAsymptotics HardSaddleGrowth
  BalancedReciprocalSaddleCost OddPrimePivot ReciprocalOddPivots ExponentialIntegral

theorem uniform_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      pivotSum (3 * N) + 1 ≤ (N : ℝ) *
        Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  let θ := ε / 4
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  obtain ⟨NC, hCount⟩ := FineSaddlePivotCount.uniform_population_bound θ hθ
  obtain ⟨HC, hCost⟩ := uniform_cost_lower θ hθ
  let F := 9 / θ + 7
  have hF : 0 < F := by dsimp only [F]; positivity
  obtain ⟨NP, hPref⟩ := SaddleLogPrefactors.logarithmic_power F hF 1 θ hθ
  obtain ⟨NE, hError⟩ := CoarseSaddlePowerErrors.power_negligible 1 0 2 1 (by norm_num) (by norm_num)
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NG, hG⟩ := eventually_atTop.mp (hlogT.eventually
    ((eventually_ge_atTop (max HC (max (saddleThreshold 1) 1))).and
      (((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).eventually
        (eventually_ge_atTop (1 : ℝ))).and
        (((tendsto_saddleParameter_div_nu (by norm_num : (0 : ℝ) < 1)).eventually
          (eventually_lt_nhds (by positivity : (0 : ℝ) < θ / 2))).and
          ((tendsto_nu_div_cutoff.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / θ))).and
            (tendsto_cutoff_div_height.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))))))))
  refine ⟨max NC (max NP (max NE NG)), ?_⟩
  intro N hN
  let H := Real.log (N : ℝ)
  let u := saddleParameter 1 H
  let V := saddleCutoff 1 H
  let ν := saddleNu 1 H
  let E := exponentialIntegral u
  let w := θ * ν
  let K := ⌈3 * V / w⌉₊
  obtain ⟨hbase, hν1, huν, hνV, hVH⟩ := hG N (by omega)
  have hHC : HC ≤ H := (le_max_left _ _).trans hbase
  have hroot : saddleThreshold 1 ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hbase)
  have hH1 : 1 ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hbase)
  have hH : 0 < H := by linarith only [hH1]
  have hV : 0 < V := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  have hν : 0 < ν := div_pos hH hV
  have hw : 0 < w := mul_pos hθ hν
  have hwθ : θ ≤ w := by change 1 ≤ ν at hν1; dsimp only [w]; nlinarith only [hν1, hθ]
  have huwidth : 2 * u ≤ w := by
    have hh := (div_le_iff₀ hν).mp huν.le
    change u ≤ θ / 2 * ν at hh
    dsimp only [w]
    linarith only [hh]
  have hwV : w ≤ V := by
    have hh := (div_le_iff₀ hV).mp hνV.le
    change ν ≤ (1 / θ) * V at hh
    have hm := mul_le_mul_of_nonneg_right hh hθ.le
    have hid : ((1 / θ) * V) * θ = V := by field_simp
    rw [hid] at hm
    dsimp only [w]
    nlinarith only [hm]
  have h4V : 4 * V ≤ H := by
    have hh := (div_le_iff₀ hH).mp hVH.le
    change V ≤ (1 / 4 : ℝ) * H at hh
    linarith only [hh]
  have hK : 1 ≤ K := Nat.one_le_ceil_iff.mpr (by positivity)
  have hKlo : 3 * V ≤ (K : ℝ) * w := (div_le_iff₀ hw).mp (Nat.le_ceil (3 * V / w))
  have hKhi : (K : ℝ) ≤ 3 * V / w + 1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 3 * V / w)).le
  have hKwidth : (K : ℝ) * w ≤ H := by
    have hh := mul_le_mul_of_nonneg_right hKhi hw.le
    have hid : (3 * V / w + 1) * w = 3 * V + w := by field_simp
    rw [hid] at hh
    linarith only [hh, hwV, h4V]
  have hcounts (j : Fin K) :
      (((Icc 1 (3 * N)).filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) * w))).card : ℝ) ≤
        3 * N * Real.exp (-H * u / (((j.val + 1 : ℕ) : ℝ) * w) + E + w) := by
    have hvlo : 2 * u ≤ ((j.val + 1 : ℕ) : ℝ) * w := by
      have hj : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ j.val + 1 by omega)
      exact huwidth.trans (by nlinarith only [hj, hw])
    have hvhi : ((j.val + 1 : ℕ) : ℝ) * w ≤ H := by
      have hj : ((j.val + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show j.val + 1 ≤ K by omega)
      exact (mul_le_mul_of_nonneg_right hj hw.le).trans hKwidth
    apply hCount N (by omega) (((j.val + 1 : ℕ) : ℝ) * w) hvlo hvhi
      ((Icc 1 (3 * N)).filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) * w)))
      (filter_subset _ _)
    intro n hn
    exact (mem_filter.mp hn).2
  have hmass := MovingLogarithmicPivotMass.finite_mass N K hK w H u E V w hw hV hw.le hKlo
    (Icc 1 (3 * N)) (Subset.refl _) (hCost H hHC) hcounts
  have hmass' : pivotSum (3 * N) ≤ (3 * (K : ℝ) + 3) * N * Real.exp (-2 * V + 3 * w) := by
    change pivotSum (3 * N) ≤ _ at hmass
    have hid : -2 * V + w + 2 * w = -2 * V + 3 * w := by ring
    simpa only [hid] using hmass
  have hone : 1 ≤ (N : ℝ) * Real.exp (-2 * V + 3 * w) := by
    have he := hError N (by omega)
    simp only [Real.rpow_zero, Real.rpow_one, one_mul] at he
    have hh : -2 * V ≤ -2 * V + 3 * w := by linarith only [hw]
    exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh) (Nat.cast_nonneg N))
  have hsum : pivotSum (3 * N) + 1 ≤ (3 * (K : ℝ) + 4) * N * Real.exp (-2 * V + 3 * w) := by
    nlinarith only [hmass', hone]
  have hKbound : (K : ℝ) ≤ 3 * H / θ + 1 := by
    have hd := div_le_div_of_nonneg_left (by positivity : 0 ≤ 3 * V) hθ hwθ
    have hvh : V ≤ H := by linarith only [h4V, hV]
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvh (by norm_num : (0 : ℝ) ≤ 3)) hθ.le
    linarith only [hKhi, hd, hh]
  have hpoly : 3 * (K : ℝ) + 4 ≤ F * H := by
    have hh := mul_le_mul_of_nonneg_left hKbound (by norm_num : (0 : ℝ) ≤ 3)
    dsimp only [F]
    have hid : (9 / θ + 7) * H = 3 * (3 * H / θ + 1) + 4 + 7 * (H - 1) := by ring
    rw [hid]
    linarith only [hh, hH1]
  have hpref : 3 * (K : ℝ) + 4 ≤ Real.exp w := by
    have hh := hPref N (by omega)
    simp only [pow_one] at hh
    exact hpoly.trans hh
  calc
    _ ≤ (3 * (K : ℝ) + 4) * N * Real.exp (-2 * V + 3 * w) := hsum
    _ ≤ Real.exp w * N * Real.exp (-2 * V + 3 * w) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref (Nat.cast_nonneg N)) (Real.exp_nonneg _)
    _ = (N : ℝ) * (Real.exp w * Real.exp (-2 * V + 3 * w)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      dsimp only [w, θ]
      ring

theorem uniform_population_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ S : Finset ℕ, S ⊆ Icc 1 (3 * N) →
      (∑ n ∈ S, 1 / (largestOddPrime n : ℝ)) + 1 ≤
        (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  obtain ⟨N₀, h⟩ := uniform_upper ε hε
  refine ⟨N₀, ?_⟩
  intro N hN S hS
  have hsum : (∑ n ∈ S, 1 / (largestOddPrime n : ℝ)) ≤ pivotSum (3 * N) :=
    sum_le_sum_of_subset_of_nonneg hS (by intros; positivity)
  have hh := h N hN
  linarith only [hsum, hh]

theorem uniform_original_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      primeSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) ∧
      pivotSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) ∧
      DyadicOddPivots.dyadicSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
  obtain ⟨N₀, h⟩ := uniform_population_upper ε hε
  refine ⟨N₀, ?_⟩
  intro N hN
  have hfull := h N hN (Icc 1 N) (by intro n hn; obtain ⟨hl, hu⟩ := mem_Icc.mp hn; exact mem_Icc.mpr ⟨hl, by omega⟩)
  have hdyadic := h N hN (Ico N (2 * N)) (by
    intro n hn
    obtain ⟨hl, hu⟩ := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩)
  have hfull' : pivotSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
    change pivotSum N + 1 ≤ _ at hfull
    linarith only [hfull]
  have hdyadic' : DyadicOddPivots.dyadicSum N ≤ (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
    change DyadicOddPivots.dyadicSum N + 1 ≤ _ at hdyadic
    linarith only [hdyadic]
  exact ⟨(primeSum_le_pivotSum N).trans hfull', hfull', hdyadic'⟩


end PaperP1.FineReciprocalUpper
