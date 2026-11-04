module

public import PaperP1.Asymptotics.SignedSaddleCostUpper
public import PaperP1.Asymptotics.SignedPrescribedSaddleLower
public import PaperP1.Asymptotics.EnlargedRawValueProfileUnderInputs

/-! # Both directions of companion T19.16 for the literal prescribed signed forcing

The ordinary EIP estimate and the six existing geometric inputs are
explicit. The geometric bundle is fixed before the requested error margin.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedSaddleCostTheorem

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.OrdinaryReciprocalPrimeInput
  PaperP1.SignedPrivateDyadicField PaperP1.SignedPrivateField PaperP1.SignedSaddleExcess

def specifiedCost (N L : ℕ) : ℝ :=
  if hN : 2 ≤ N then
    if hL : 1 ≤ L then cost (data (E := excess N) hN hL) else 0
  else 0

theorem specifiedCost_eq {N L : ℕ} (hN : 2 ≤ N) (hL : 1 ≤ L) :
    specifiedCost N L = cost (data (E := excess N) hN hL) := by
  simp only [specifiedCost, dite_eq_left hN, dite_eq_left hL]

theorem log_error_of_sandwich {c V ν ε : ℝ}
    (hl : Real.exp (-2 * V - ε * ν) ≤ c) (hu : c ≤ Real.exp (-2 * V + ε * ν)) :
    |Real.log c + 2 * V| ≤ ε * ν := by
  have hc : 0 < c := (Real.exp_pos _).trans_le hl
  have hlow := Real.log_le_log (Real.exp_pos _) hl
  have hhigh := Real.log_le_log hc hu
  simp only [Real.log_exp] at hlow hhigh
  exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hhigh]⟩

structure Conclusion (C : ℝ) : Prop where
  saddle_cost : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
    1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ specifiedCost N L ∧
      specifiedCost N L ≤ Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N))
  logarithmic_cost : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
    1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |Real.log (specifiedCost N L) + 2 * saddleCutoff 1 (Real.log N)| ≤ ε * saddleNu 1 (Real.log N)
  power_obstruction : ∀ α K : ℝ, 0 < α → 0 < K → ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
    1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      K * (N : ℝ) ^ (-α) ≤ specifiedCost N L

theorem uniform_power_obstruction (hinput : EIPInput) (C α K : ℝ) (hα : 0 < α) (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        K * (N : ℝ) ^ (-α) ≤ specifiedCost N L := by
  obtain ⟨N₀, h⟩ := SignedPrescribedSaddleLower.uniform_power_obstruction hinput C α K hα hK
  refine ⟨N₀, ?_⟩
  intro N hN L hL hcrit
  rw [specifiedCost_eq (by omega) hL]
  exact h N hN L hL hcrit

theorem not_bigO_critical_sequence (hinput : EIPInput) (C : ℝ) (length : ℕ → ℕ)
    (hseq : ∀ᶠ N : ℕ in atTop, 1 ≤ length N ∧
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C) (α : ℝ) (hα : 0 < α) :
    ¬ Asymptotics.IsBigO atTop (fun N ↦ specifiedCost N (length N)) (fun N ↦ (N : ℝ) ^ (-α)) := by
  intro h
  obtain ⟨K, hbound⟩ := h.bound
  have hK : 0 < |K| + 1 := by have := abs_nonneg K; linarith
  obtain ⟨N₀, hLower⟩ := uniform_power_obstruction hinput C α (|K| + 1) hα hK
  have hfalse : ∀ᶠ N : ℕ in atTop, False := by
    filter_upwards [hseq, hbound, eventually_ge_atTop (max N₀ 2)] with N hs hb hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hp : 0 < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos hn _
    have hl := hLower N hN (length N) hs.1 hs.2
    have hc : 0 ≤ specifiedCost N (length N) := (mul_pos hK hp).le.trans hl
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_pos hp] at hb
    have hh := mul_le_mul_of_nonneg_right (le_abs_self K) hp.le
    nlinarith only [hl, hb, hh, hp]
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

theorem companion_T19_16 (hinput : EIPInput) (C : ℝ) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap (1 / 12288)) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) → Conclusion C) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hProfile⟩ :=
    EnlargedRawValueProfileUnderInputs.uniform_profile C (1 / 12) (by norm_num)
  rw [show (1 / 12 : ℝ) / 1024 = 1 / 12288 by norm_num] at hProfile
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hCurve hCurve₁ hCurve₂
  obtain ⟨NP, hP⟩ := hProfile hCover hCover₁ hCover₂ hCurve hCurve₁ hCurve₂
  obtain ⟨NW, hW⟩ := uniform_width C
  have hBoth (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      1 ≤ L → |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ specifiedCost N L ∧
        specifiedCost N L ≤ Real.exp (-2 * saddleCutoff 1 (Real.log N) + ε * saddleNu 1 (Real.log N)) := by
    obtain ⟨NL, hLower⟩ := SignedPrescribedSaddleLower.uniform_actual_lower hinput C ε hε
    obtain ⟨NU, hUpper⟩ := SignedSaddleCostUpper.uniform_upper_from_profile hinput C
      widthConstant widthConstant_pos ε hε
    refine ⟨max NL (max NU (max NP NW)), ?_⟩
    intro N hN L hL hcrit
    rw [specifiedCost_eq (by omega) hL]
    refine ⟨hLower N (by omega) L hL hcrit, hUpper N (by omega) L (excess N) hL hcrit
      (hW N (by omega) L hcrit) ?_⟩
    simpa only [show (3 : ℝ) / 2 + 1 / 12 = 19 / 12 by norm_num] using hP N (by omega) L hcrit
  refine ⟨hBoth, ?_, uniform_power_obstruction hinput C⟩
  intro ε hε
  obtain ⟨N₀, h⟩ := hBoth ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL hcrit
  exact log_error_of_sandwich (h N hN L hL hcrit).1 (h N hN L hL hcrit).2

theorem normalized_log_limit {C : ℝ} (h : Conclusion C) (length : ℕ → ℕ)
    (hseq : ∀ᶠ N : ℕ in atTop, 1 ≤ length N ∧
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C) :
    Tendsto (fun N : ℕ ↦
      (Real.log (specifiedCost N (length N)) + 2 * saddleCutoff 1 (Real.log N)) /
        saddleNu 1 (Real.log N)) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨NL, hL⟩ := h.logarithmic_cost (ε / 2) (by positivity)
  obtain ⟨NS, hS⟩ := eventually_atTop.mp hseq
  have hnlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).comp hnlog
  obtain ⟨NN, hNu⟩ := eventually_atTop.mp (ht.eventually (eventually_gt_atTop (0 : ℝ)))
  refine ⟨max NL (max NS (max NN 2)), ?_⟩
  intro N hN
  have hnu := hNu N (by omega)
  change 0 < saddleNu 1 (Real.log N) at hnu
  have hl := hL N (by omega) (length N) (hS N (by omega)).1 (hS N (by omega)).2
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hnu]
  exact ((div_le_iff₀ hnu).mpr hl).trans_lt (by linarith only [hε])

end PaperP1.SignedSaddleCostTheorem
