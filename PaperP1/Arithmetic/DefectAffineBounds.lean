module

public import PaperP1.Arithmetic.DefectAffineIntervals

@[expose] public section

/-! # Fixed dilation and translation versions of the defect bounds -/

namespace PaperP1.DefectAffineBounds

open Finset DefectAffineIntervals LocalDefectBound

theorem affine_local_defect_bound_eventually
    (a shift c C b Bmax Hscale Rscale : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hC : 0 < C) (hb : 0 < b) (hBmax : 0 ≤ Bmax)
    (hHscale : 0 ≤ Hscale) (hRscale : 0 ≤ Rscale) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℝ, ∀ H U R : ℕ,
      b * Real.log N ≤ B → B ≤ Bmax * Real.log N →
      (H : ℝ) ≤ Hscale * B → (R : ℝ) ≤ Rscale * B →
      c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
      ((affineIntervalDefects a shift H U R).card : ℝ) ≤ K * B / Real.log B := by
  obtain ⟨K, hK, Ncore, hcore⟩ :=
    LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
      (a * c / 2) (a * C + |shift| + 1) b Bmax Hscale (a * Rscale + 1)
      (by positivity) (by positivity) hb hBmax hHscale (by positivity)
  obtain ⟨Nlog, hNlog⟩ := ElementaryLogGrowth.log_ge_eventually (1 / b + 1)
  refine ⟨K, hK, max Ncore (max Nlog (max 1 ⌈2 * |shift| / (a * c)⌉₊)), ?_⟩
  intro N hN B H U R hBlo hBhi hH hR hUlo hUhi
  have hNcore : Ncore ≤ N := (le_max_left _ _).trans hN
  have htail : max Nlog (max 1 ⌈2 * |shift| / (a * c)⌉₊) ≤ N :=
    (le_max_right _ _).trans hN
  have hNlog' : Nlog ≤ N := (le_max_left _ _).trans htail
  have hbasic : max 1 ⌈2 * |shift| / (a * c)⌉₊ ≤ N :=
    (le_max_right _ _).trans htail
  have hNone : 1 ≤ N := (le_max_left _ _).trans hbasic
  have hshift : 2 * |shift| / (a * c) ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈2 * |shift| / (a * c)⌉₊).trans hbasic)
  have hlog : 1 / b + 1 ≤ Real.log (N : ℝ) := (hNlog N hNlog').1
  have hBone : 1 ≤ B := by
    have hs : 1 / b ≤ Real.log (N : ℝ) := by linarith
    have hmul := (div_le_iff₀ hb).mp hs
    nlinarith
  have hbase := affineBase_bounds ha hc hC hNone hshift hUlo hUhi
  have hwidth := affineWidth_le_window ha.le hBone hR
  have hcount := hcore N hNcore B H (affineBase a shift U) (affineWidth a R)
    hBlo hBhi hH hwidth hbase.2.1 hbase.2.2
  have hcard : (affineIntervalDefects a shift H U R).card ≤
      (defectsInInterval H (affineBase a shift U) (affineWidth a R)).card :=
    card_le_card affineIntervalDefects_subset
  exact (by exact_mod_cast hcard : ((affineIntervalDefects a shift H U R).card : ℝ) ≤
    ((defectsInInterval H (affineBase a shift U) (affineWidth a R)).card : ℝ)).trans hcount

theorem affineIntervalDefects_subset_positiveBelow
    {a shift : ℝ} {H U R : ℕ} :
    affineIntervalDefects a shift H U R ⊆
      GlobalDefectCount.positiveDefectsBelow H (affineHeight a shift (U + R)) := by
  intro n hn
  obtain ⟨hnpos, _hnlo, hnhi, hdef⟩ := mem_affineIntervalDefects.mp hn
  exact GlobalDefectCount.mem_positiveDefectsBelow.mpr
    ⟨ne_of_gt hnpos, Nat.le_floor hnhi, hdef⟩

/-- Positive defective values up to every fixed affine-transformed endpoint
have the same uniform global exponent. This also bounds every subinterval. -/
theorem affine_global_defect_cover_bound_eventually
    (a shift C D : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H X : ℕ,
      (H : ℝ) ≤ D * Real.log N → (X : ℝ) ≤ C * N →
      ((GlobalDefectCount.positiveDefectsBelow H (affineHeight a shift X)).card : ℝ) ≤
        (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨Ncore, hcore⟩ := GlobalDefectCount.global_defect_count_le_rpow_eventually
    (a * C + |shift| + 1) D (by positivity) hD ε hε
  refine ⟨max Ncore 1, ?_⟩
  intro N hN H X hH hX
  have hNone : 1 ≤ N := (le_max_right _ _).trans hN
  exact hcore N ((le_max_left _ _).trans hN) H (affineHeight a shift X) hH
    (affineHeight_le_linear ha.le hC hNone hX)

theorem affine_global_interval_defect_bound_eventually
    (a shift C D : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H X : ℕ,
      (H : ℝ) ≤ D * Real.log N → (X : ℝ) ≤ C * N →
      ((affineIntervalDefects a shift H 0 X).card : ℝ) ≤
        (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := affine_global_defect_cover_bound_eventually a shift C D ha hC hD ε hε
  refine ⟨N₀, ?_⟩
  intro N hN H X hH hX
  have hcard : (affineIntervalDefects a shift H 0 X).card ≤
      (GlobalDefectCount.positiveDefectsBelow H (affineHeight a shift X)).card := by
    simpa only [Nat.zero_add] using
      card_le_card (affineIntervalDefects_subset_positiveBelow (a := a) (shift := shift)
        (H := H) (U := 0) (R := X))
  exact (by exact_mod_cast hcard : ((affineIntervalDefects a shift H 0 X).card : ℝ) ≤
    ((GlobalDefectCount.positiveDefectsBelow H (affineHeight a shift X)).card : ℝ)).trans
      (hN₀ N hN H X hH hX)

/-- All positive base points up to the affine endpoint, with the scaled
real width rounded up, satisfy the uniform two-defect count. -/
theorem affine_two_defect_cover_bound_eventually
    (a shift C D E : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H R X : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (R : ℝ) ≤ E * Real.log N → (X : ℝ) ≤ C * N →
      ((TwoDefectHosts.twoDefectStarts H (affineWidth a R) (affineHeight a shift X)).card : ℝ) ≤
        (N : ℝ) ^ ε := by
  obtain ⟨Ncore, hcore⟩ := TwoDefectCount.two_defect_count_le_rpow_eventually
    (a * C + |shift| + 1) D (a * E + 1) (by positivity) hD (by positivity) ε hε
  obtain ⟨Nlog, hNlog⟩ := ElementaryLogGrowth.log_ge_eventually 1
  refine ⟨max Ncore Nlog, ?_⟩
  intro N hN H R X hH hR hX
  have hlog := hNlog N ((le_max_right _ _).trans hN)
  have hNone : 1 ≤ N := by omega
  exact hcore N ((le_max_left _ _).trans hN) H (affineWidth a R) (affineHeight a shift X)
    hH (affineWidth_le_log ha.le hlog.1 hR)
    (affineHeight_le_linear ha.le hC hNone hX)

end PaperP1.DefectAffineBounds

