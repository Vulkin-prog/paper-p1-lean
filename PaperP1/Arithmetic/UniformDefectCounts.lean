module

public import PaperP1.Arithmetic.DefectAffineWindows
public import PaperP1.Arithmetic.TwoDefectWindows

@[expose] public section

/-!
# Companion T1.3: local, global and two-defect counts

All constants and thresholds precede every scale, cutoff, interval and length.
The lower comparison for H in the manuscript is unnecessary.
-/

namespace PaperP1.UniformDefectCounts

open LocalDefectBound DefectAffineIntervals

theorem bound_of_window_comparison
    {N n : ℕ} {B scale Bmax : ℝ} (hscale : 0 ≤ scale)
    (hn : (n : ℝ) ≤ scale * B) (hB : B ≤ Bmax * Real.log N) :
    (n : ℝ) ≤ (scale * Bmax) * Real.log N := by
  calc
    _ ≤ scale * B := hn
    _ ≤ scale * (Bmax * Real.log N) := mul_le_mul_of_nonneg_left hB hscale
    _ = _ := by ring

/-- Complete companion T1.3 on the original integer intervals and exact
dyadic vertex windows. The lower cutoff comparison H ≳ B is not needed. -/
theorem companion_T1_3
    (c C b Bmax Hscale Rscale : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hb : 0 < b) (hBmax : 0 ≤ Bmax)
    (hHscale : 0 ≤ Hscale) (hRscale : 0 ≤ Rscale) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℝ, ∀ H : ℕ,
        b * Real.log N ≤ B → B ≤ Bmax * Real.log N →
        (H : ℝ) ≤ Hscale * B →
        (∀ U R : ℕ, (R : ℝ) ≤ Rscale * B →
          c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
          ((defectsInInterval H U R).card : ℝ) ≤ K * B / Real.log B) ∧
        (∀ X : ℕ, (X : ℝ) ≤ C * N →
          ((GlobalDefectCount.positiveDefectsBelow H X).card : ℝ) ≤
            (N : ℝ) ^ (1 / 2 + ε)) ∧
        (∀ L : ℕ, (L : ℝ) ≤ Rscale * B →
          ((TwoDefectWindows.dyadicTwoDefectWindows N H L).card : ℝ) ≤ (N : ℝ) ^ ε) := by
  obtain ⟨K, hK, Nlocal, hlocal⟩ :=
    LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
      c C b Bmax Hscale Rscale hc hC hb hBmax hHscale hRscale
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨Nglobal, hglobal⟩ := GlobalDefectCount.global_defect_count_le_rpow_eventually
    C (Hscale * Bmax) hC.le (mul_nonneg hHscale hBmax) ε hε
  obtain ⟨Ntwo, htwo⟩ := TwoDefectWindows.dyadic_two_defect_windows_le_rpow_eventually
    (Hscale * Bmax) (Rscale * Bmax)
    (mul_nonneg hHscale hBmax) (mul_nonneg hRscale hBmax) ε hε
  refine ⟨max Nlocal (max Nglobal Ntwo), ?_⟩
  intro N hN B H hBlo hBhi hH
  have hNl : Nlocal ≤ N := (le_max_left _ _).trans hN
  have htail : max Nglobal Ntwo ≤ N := (le_max_right _ _).trans hN
  have hNg : Nglobal ≤ N := (le_max_left _ _).trans htail
  have hNt : Ntwo ≤ N := (le_max_right _ _).trans htail
  have hHlog := bound_of_window_comparison hHscale hH hBhi
  refine ⟨?_, ?_, ?_⟩
  · intro U R hR hUlo hUhi
    exact hlocal N hNl B H U R hBlo hBhi hH hR hUlo hUhi
  · intro X hX
    exact hglobal N hNg H X hHlog hX
  · intro L hL
    exact htwo N hNt H L hHlog (bound_of_window_comparison hRscale hL hBhi)

/-- Complete fixed real affine version. The scale a>0 and translation are
fixed before the common constant and all thresholds. The global interval is
[shift, a C N+shift]; the dyadic vertex window is [y-a,y-a+aL]. -/
theorem companion_T1_3_fixed_affine
    (a shift c C b Bmax Hscale Rscale : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hC : 0 < C) (hb : 0 < b) (hBmax : 0 ≤ Bmax)
    (hHscale : 0 ≤ Hscale) (hRscale : 0 ≤ Rscale) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ B : ℝ, ∀ H : ℕ,
        b * Real.log N ≤ B → B ≤ Bmax * Real.log N →
        (H : ℝ) ≤ Hscale * B →
        (∀ U R : ℕ, (R : ℝ) ≤ Rscale * B →
          c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
          ((affineIntervalDefects a shift H U R).card : ℝ) ≤ K * B / Real.log B) ∧
        ((affineIntervalDefects (a * C) shift H 0 N).card : ℝ) ≤
          (N : ℝ) ^ (1 / 2 + ε) ∧
        (∀ L : ℕ, (L : ℝ) ≤ Rscale * B →
          ((DefectAffineWindows.affineDyadicTwoDefectWindows a shift N H L).card : ℝ) ≤
            (N : ℝ) ^ ε) := by
  obtain ⟨K, hK, Nlocal, hlocal⟩ := DefectAffineBounds.affine_local_defect_bound_eventually
    a shift c C b Bmax Hscale Rscale ha hc hC hb hBmax hHscale hRscale
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨Nglobal, hglobal⟩ := DefectAffineBounds.affine_global_interval_defect_bound_eventually
    (a * C) shift 1 (Hscale * Bmax) (mul_pos ha hC) (by norm_num)
    (mul_nonneg hHscale hBmax) ε hε
  obtain ⟨Ntwo, htwo⟩ :=
    DefectAffineWindows.affine_dyadic_two_defect_windows_le_rpow_eventually
      a shift (Hscale * Bmax) (Rscale * Bmax) ha
      (mul_nonneg hHscale hBmax) (mul_nonneg hRscale hBmax) ε hε
  refine ⟨max Nlocal (max Nglobal Ntwo), ?_⟩
  intro N hN B H hBlo hBhi hH
  have hNl : Nlocal ≤ N := (le_max_left _ _).trans hN
  have htail : max Nglobal Ntwo ≤ N := (le_max_right _ _).trans hN
  have hNg : Nglobal ≤ N := (le_max_left _ _).trans htail
  have hNt : Ntwo ≤ N := (le_max_right _ _).trans htail
  have hHlog := bound_of_window_comparison hHscale hH hBhi
  refine ⟨?_, ?_, ?_⟩
  · intro U R hR hUlo hUhi
    exact hlocal N hNl B H U R hBlo hBhi hH hR hUlo hUhi
  · exact hglobal N hNg H N hHlog (by norm_num)
  · intro L hL
    exact htwo N hNt H L hHlog (bound_of_window_comparison hRscale hL hBhi)

/-- Literal run-length convention B=L+1 from the manuscript. -/
theorem companion_T1_3_run_length
    (c C b Bmax Hscale Rscale : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hb : 0 < b) (hBmax : 0 ≤ Bmax)
    (hHscale : 0 ≤ Hscale) (_hRscale : 0 ≤ Rscale) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H L : ℕ,
        b * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ Bmax * Real.log N →
        (H : ℝ) ≤ Hscale * (L + 1 : ℝ) →
        (∀ U R : ℕ, (R : ℝ) ≤ Rscale * (L + 1 : ℝ) →
          c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
          ((defectsInInterval H U R).card : ℝ) ≤ K * (L + 1 : ℝ) / Real.log (L + 1 : ℝ)) ∧
        (∀ X : ℕ, (X : ℝ) ≤ C * N →
          ((GlobalDefectCount.positiveDefectsBelow H X).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε)) ∧
        ((TwoDefectWindows.dyadicTwoDefectWindows N H L).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨K, hK, hcore⟩ := companion_T1_3 c C b Bmax Hscale (max Rscale 1)
    hc hC hb hBmax hHscale (by positivity)
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hcore ε hε
  refine ⟨N₀, ?_⟩
  intro N hN H L hBlo hBhi hH
  have hresult := hN₀ N hN (L + 1 : ℝ) H hBlo hBhi hH
  have hB0 : (0 : ℝ) ≤ L + 1 := by positivity
  have hRbig : Rscale * (L + 1 : ℝ) ≤ max Rscale 1 * (L + 1 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hB0
  have hLbig : (L : ℝ) ≤ max Rscale 1 * (L + 1 : ℝ) := by
    have hmax : (1 : ℝ) ≤ max Rscale 1 := le_max_right _ _
    nlinarith
  exact ⟨fun U R hR hUlo hUhi => hresult.1 U R (hR.trans hRbig) hUlo hUhi,
    hresult.2.1, hresult.2.2 L hLbig⟩

/-- Literal B=L+1 convention after any fixed positive real dilation and
fixed real translation of the intervals. -/
theorem companion_T1_3_run_length_fixed_affine
    (a shift c C b Bmax Hscale Rscale : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hC : 0 < C) (hb : 0 < b) (hBmax : 0 ≤ Bmax)
    (hHscale : 0 ≤ Hscale) (_hRscale : 0 ≤ Rscale) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H L : ℕ,
        b * Real.log N ≤ (L + 1 : ℝ) → (L + 1 : ℝ) ≤ Bmax * Real.log N →
        (H : ℝ) ≤ Hscale * (L + 1 : ℝ) →
        (∀ U R : ℕ, (R : ℝ) ≤ Rscale * (L + 1 : ℝ) →
          c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
          ((affineIntervalDefects a shift H U R).card : ℝ) ≤
            K * (L + 1 : ℝ) / Real.log (L + 1 : ℝ)) ∧
        ((affineIntervalDefects (a * C) shift H 0 N).card : ℝ) ≤
          (N : ℝ) ^ (1 / 2 + ε) ∧
        ((DefectAffineWindows.affineDyadicTwoDefectWindows a shift N H L).card : ℝ) ≤
          (N : ℝ) ^ ε := by
  obtain ⟨K, hK, hcore⟩ := companion_T1_3_fixed_affine a shift c C b Bmax Hscale
    (max Rscale 1) ha hc hC hb hBmax hHscale (by positivity)
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hcore ε hε
  refine ⟨N₀, ?_⟩
  intro N hN H L hBlo hBhi hH
  have hresult := hN₀ N hN (L + 1 : ℝ) H hBlo hBhi hH
  have hB0 : (0 : ℝ) ≤ L + 1 := by positivity
  have hRbig : Rscale * (L + 1 : ℝ) ≤ max Rscale 1 * (L + 1 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hB0
  have hLbig : (L : ℝ) ≤ max Rscale 1 * (L + 1 : ℝ) := by
    have hmax : (1 : ℝ) ≤ max Rscale 1 := le_max_right _ _
    nlinarith
  exact ⟨fun U R hR hUlo hUhi => hresult.1 U R (hR.trans hRbig) hUlo hUhi,
    hresult.2.1, hresult.2.2 L hLbig⟩

end PaperP1.UniformDefectCounts

