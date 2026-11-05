module

public import PaperP1.Analysis.FiniteLogarithmicPivotMass
public import PaperP1.Asymptotics.ScaledSaddlePivotCount
public import PaperP1.Arithmetic.DyadicOddPivots

/-! # A one-sided sharp leading coefficient for actual reciprocal pivots

For every fixed c<2 the upper bound is N exp(-cV_N). This does not
supply the matching lower coefficient or the fine o(nu_N) equivalent.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StratifiedReciprocalUpper

open Finset Filter SaddleParameters SaddleScales HardSaddleGrowth OddPrimePivot ReciprocalOddPivots

theorem uniform_upper (c : ℝ) (hc2 : c < 2) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      pivotSum (3 * N) + 1 ≤ (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) := by
  let d := 2 - c
  have hd : 0 < d := by dsimp only [d]; linarith only [hc2]
  let η := min (d / 4) (1 / 12)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηd : η ≤ d / 4 := min_le_left _ _
  have hηsmall : η ≤ 1 / 12 := min_le_right _ _
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (4 / d))
  have hK1 : 1 ≤ K := by have hh := (le_max_left _ _).trans_lt hK; exact_mod_cast hh.le
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKinv : 1 / (K : ℝ) ≤ d / 4 := by
    have hh := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hK)
    exact (div_le_iff₀ hKpos).mpr (by nlinarith only [hh])
  let c₀ := 2 - 1 / (K : ℝ) - η
  let g := c₀ - c
  have hcc : c < c₀ := by dsimp only [c₀, d] at *; linarith only [hKinv, hηd, hc2]
  have hg : 0 < g := by dsimp only [g]; linarith only [hcc]
  have hc₀ : c₀ ≤ 2 := by
    have hi : 0 ≤ 1 / (K : ℝ) := by positivity
    dsimp only [c₀]
    linarith only [hi, hη]
  let A (j : Fin (3 * K)) : ℝ := ((j.val + 1 : ℕ) : ℝ) / K
  let b (j : Fin (3 * K)) : ℝ := 1 / A j - η
  have hApos (j : Fin (3 * K)) : 0 < A j := by dsimp only [A]; positivity
  have hA3 (j : Fin (3 * K)) : A j ≤ 3 := by
    apply (div_le_iff₀ hKpos).mpr
    have hh : ((j.val + 1 : ℕ) : ℝ) ≤ ((3 * K : ℕ) : ℝ) := by exact_mod_cast (show j.val + 1 ≤ 3 * K by omega)
    push_cast at hh ⊢
    nlinarith only [hh]
  have hbpos (j : Fin (3 * K)) : 0 < b j := by
    have hh : (1 / 3 : ℝ) ≤ 1 / A j := one_div_le_one_div_of_le (hApos j) (hA3 j)
    dsimp only [b]
    linarith only [hh, hηsmall]
  have hblt (j : Fin (3 * K)) : b j < 1 / A j := by dsimp only [b]; linarith only [hη]
  have hEach (j : Fin (3 * K)) := ScaledSaddlePivotCount.uniform_population_bound
    (A j) (b j) (hApos j) (hbpos j) (hblt j)
  choose Nc hCount using hEach
  obtain ⟨HB, hbnd⟩ := square_band_eventually
  let F : ℝ := 3 * K + 4
  have hF : 0 < F := by dsimp only [F]; positivity
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hVT := tendsto_cutoff_atTop.comp hlogT
  obtain ⟨NG, hG⟩ := eventually_atTop.mp
    ((hlogT.eventually (eventually_ge_atTop HB)).and
      (((tendsto_cutoff_div_height.comp hlogT).eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
          (hVT.eventually (eventually_ge_atTop (Real.log F / g)))))
  refine ⟨max (univ.sup Nc) NG, ?_⟩
  intro N hN
  let H := Real.log (N : ℝ)
  let V := saddleCutoff 1 H
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨hHB, hVH, hlarge⟩ := hG N (by omega)
  obtain ⟨hHp, hVp, _hsq, _hsq'⟩ := hbnd H hHB
  have hwidth : 2 * V ≤ H := by
    have hh := (div_le_iff₀ hHp).mp hVH.le
    change V ≤ (1 / 2 : ℝ) * H at hh
    linarith only [hh]
  have hcounts (j : Fin (3 * K)) :
      (((Icc 1 (3 * N)).filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (((j.val + 1 : ℕ) : ℝ) / K * V))).card : ℝ) ≤
        (N : ℝ) * Real.exp (-(1 / (((j.val + 1 : ℕ) : ℝ) / K) - η) * V) := by
    have hNj : Nc j ≤ N := (le_sup (f := Nc) (mem_univ j)).trans (by omega)
    apply hCount j N (by omega)
      ((Icc 1 (3 * N)).filter (fun n ↦ (largestOddPrime n : ℝ) ≤ Real.exp (A j * V)))
      (filter_subset _ _)
    intro n hnS
    exact (mem_filter.mp hnS).2
  have hmass := FiniteLogarithmicPivotMass.finite_mass N K hK1 V η hVp hη.le (Icc 1 (3 * N)) (Subset.refl _) hcounts
  change pivotSum (3 * N) ≤ (3 * (K : ℝ) + 3) * N * Real.exp (-c₀ * V) at hmass
  have hone : 1 ≤ (N : ℝ) * Real.exp (-c₀ * V) := by
    have hx := mul_le_mul_of_nonneg_right hc₀ hVp.le
    have he : (N : ℝ) * Real.exp (-c₀ * V) = Real.exp (H + -c₀ * V) := by rw [Real.exp_add, Real.exp_log hn]
    rw [he]
    exact Real.one_le_exp (by linarith only [hx, hwidth])
  have hsum : pivotSum (3 * N) + 1 ≤ F * N * Real.exp (-c₀ * V) := by
    dsimp only [F]
    nlinarith only [hmass, hone]
  have hpref : F ≤ Real.exp (g * V) := by
    have hh := (div_le_iff₀ hg).mp hlarge
    change Real.log F ≤ V * g at hh
    calc
      _ = Real.exp (Real.log F) := (Real.exp_log hF).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hh])
  calc
    _ ≤ F * N * Real.exp (-c₀ * V) := hsum
    _ ≤ Real.exp (g * V) * N * Real.exp (-c₀ * V) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref hn.le) (Real.exp_nonneg _)
    _ = (N : ℝ) * (Real.exp (g * V) * Real.exp (-c₀ * V)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; dsimp only [g]; ring

theorem uniform_population_upper (c : ℝ) (hc2 : c < 2) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ S : Finset ℕ, S ⊆ Icc 1 (3 * N) →
      (∑ n ∈ S, 1 / (largestOddPrime n : ℝ)) + 1 ≤
        (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) := by
  obtain ⟨N₀, h⟩ := uniform_upper c hc2
  refine ⟨N₀, ?_⟩
  intro N hN S hS
  have hsum : (∑ n ∈ S, 1 / (largestOddPrime n : ℝ)) ≤ pivotSum (3 * N) :=
    sum_le_sum_of_subset_of_nonneg hS (by intros; positivity)
  have hh := h N hN
  linarith only [hsum, hh]

theorem uniform_original_upper (c : ℝ) (hc2 : c < 2) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      primeSum N ≤ (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ∧
      pivotSum N ≤ (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) ∧
      DyadicOddPivots.dyadicSum N ≤ (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) := by
  obtain ⟨N₀, h⟩ := uniform_population_upper c hc2
  refine ⟨N₀, ?_⟩
  intro N hN
  have hfull := h N hN (Icc 1 N) (by intro n hn; obtain ⟨hl, hu⟩ := mem_Icc.mp hn; exact mem_Icc.mpr ⟨hl, by omega⟩)
  have hdyadic := h N hN (Ico N (2 * N)) (by
    intro n hn
    obtain ⟨hl, hu⟩ := mem_Ico.mp hn
    exact mem_Icc.mpr ⟨by omega, by omega⟩)
  have hfull' : pivotSum N ≤ (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) := by
    change pivotSum N + 1 ≤ _ at hfull
    linarith only [hfull]
  have hdyadic' : DyadicOddPivots.dyadicSum N ≤ (N : ℝ) * Real.exp (-c * saddleCutoff 1 (Real.log N)) := by
    change DyadicOddPivots.dyadicSum N + 1 ≤ _ at hdyadic
    linarith only [hdyadic]
  exact ⟨(primeSum_le_pivotSum N).trans hfull', hfull', hdyadic'⟩

end PaperP1.StratifiedReciprocalUpper
