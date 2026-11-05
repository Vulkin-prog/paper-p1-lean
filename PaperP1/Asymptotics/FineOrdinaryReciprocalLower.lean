module

public import PaperP1.Analysis.SmoothBarrierSaddleScale
public import PaperP1.Arithmetic.SmoothLowerBarrierInduction
public import PaperP1.Analysis.OrdinaryReciprocalPrimeLowerInput

/-! # Internal fine ordinary reciprocal-prime lower estimate

The actual smooth-count barrier is applied at an integer cutoff above the
actual hard saddle. All scale conditions and fixed factors are supplied.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FineOrdinaryReciprocalLower

open Filter SaddleParameters SaddleScales SaddleAsymptotics HardSaddleGrowth
  SmoothLowerBarrierProfile SmoothBarrierSaddleScale ReciprocalOddPivots
  OrdinaryReciprocalPrimeLowerInput

theorem ceil_exponential_bounds (V : ℝ) (hV : 0 ≤ V) :
    Real.exp V ≤ (⌈Real.exp V⌉₊ : ℝ) ∧ (⌈Real.exp V⌉₊ : ℝ) ≤ 2 * Real.exp V := by
  refine ⟨Nat.le_ceil _, ?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg V)).le
  have he := Real.one_le_exp hV
  linarith only [hh, he]

theorem uniform_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2,
      (N : ℝ) * Real.exp (-2 * saddleCutoff 1 (Real.log N) - ε * saddleNu 1 (Real.log N)) ≤ primeSum N := by
  let η := ε / 4
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨a, T, ha, hT, Y₀, hY₀, hsmooth⟩ := SmoothLowerBarrierInduction.uniform_lower η hη
  obtain ⟨HC, hc⟩ := eventual_cost_upper η (ε / 2) (by dsimp only [η]; linarith only [hε])
  obtain ⟨HT, ht⟩ := eventual_tilt_upper η T
  have hY₀r : (0 : ℝ) < Y₀ := by exact_mod_cast (show 0 < Y₀ by omega)
  have hlogT : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlogT.eventually
    ((eventually_ge_atTop (max HC HT)).and
      ((tendsto_cutoff_atTop.eventually (eventually_ge_atTop (Real.log Y₀))).and
        ((tendsto_saddleNu_atTop (by norm_num : (0 : ℝ) < 1)).eventually
          (eventually_ge_atTop (Real.log (2 / a) / (ε / 2)))))))
  refine ⟨N₀, ?_⟩
  intro N hN
  let H := Real.log (N : ℝ)
  let V := saddleCutoff 1 H
  let ν := saddleNu 1 H
  let Y := ⌈Real.exp V⌉₊
  obtain ⟨hbase, hVlarge, hνlarge⟩ := hN₀ N (by omega)
  obtain ⟨hroot, hTν, htilt⟩ := ht H ((le_max_right _ _).trans hbase)
  have hcost := hc H ((le_max_left _ _).trans hbase)
  have hV : 0 < V := saddleCutoff_pos (by norm_num : (0 : ℝ) < 1) hroot
  have hH : 0 < H := (saddleThreshold_pos (by norm_num : (0 : ℝ) < 1)).trans_le hroot
  have hν : 0 < ν := div_pos hH hV
  obtain ⟨hYlo, hYhi⟩ := ceil_exponential_bounds V hV.le
  have hYY₀ : Y₀ ≤ Y := by
    have hh := (Real.exp_le_exp.mpr hVlarge).trans hYlo
    rw [Real.exp_log hY₀r] at hh
    exact_mod_cast hh
  have hY : 2 ≤ Y := hY₀.trans hYY₀
  have hy : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hy0 : (0 : ℝ) < Y := by linarith only [hy]
  have hlogY : 0 < Real.log Y := Real.log_pos hy
  have hVlogY : V ≤ Real.log Y := by
    have hh := Real.log_le_log (Real.exp_pos V) hYlo
    simpa only [Real.log_exp] using hh
  have hratio : H / Real.log Y ≤ ν := div_le_div_of_nonneg_left hH.le hV hVlogY
  have hTe : Real.exp 1 ≤ T := by linarith only [hT]
  have hT1 : 1 < T := by have hh := Real.exp_pos 1; linarith only [hT, hh]
  have hmax : max T (H / Real.log Y) ≤ ν := max_le hTν hratio
  have hcap : tilt η (max T (Real.log N / Real.log Y)) ≤ Real.log Y := by
    have hm : 1 < max T (H / Real.log Y) := hT1.trans_le (le_max_left _ _)
    have hn : 1 < ν := hT1.trans_le hTν
    exact ((tilt_monotone η hm hn hmax).trans htilt).trans hVlogY
  have hcount := hsmooth Y hYY₀ N (by omega) hcap
  have hdensity : Real.exp (-cost η ν) ≤ density η T (H / Real.log Y) := by
    have hh := density_antitone η T hη.le hTe hratio
    change Real.exp (-cost η (max T ν)) ≤ density η T (H / Real.log Y) at hh
    have hTν' : T ≤ ν := hTν
    rw [max_eq_right hTν'] at hh
    exact hh
  have hcount' : a * N * Real.exp (-cost η ν) ≤ (OrdinarySmoothCensus.smoothUpTo N Y).card :=
    (mul_le_mul_of_nonneg_left hdensity (by positivity : (0 : ℝ) ≤ a * N)).trans hcount
  have hrec : a * N * Real.exp (-cost η ν) / Y ≤ primeSum N :=
    (div_le_div_of_nonneg_right hcount' hy0.le).trans (SmoothRecursiveLower.ordinary_reciprocal_lower N Y)
  have hcutoff : (a / 2) * N * Real.exp (-V - cost η ν) ≤ a * N * Real.exp (-cost η ν) / Y := by
    apply (le_div_iff₀ hy0).mpr
    calc
      _ ≤ ((a / 2) * N * Real.exp (-V - cost η ν)) * (2 * Real.exp V) :=
        mul_le_mul_of_nonneg_left hYhi (by positivity)
      _ = a * N * (Real.exp (-V - cost η ν) * Real.exp V) := by ring
      _ = a * N * Real.exp ((-V - cost η ν) + V) := by rw [← Real.exp_add]
      _ = _ := by congr 2; ring
  have hmain : (a / 2) * N * Real.exp (-2 * V - (ε / 2) * ν) ≤ primeSum N := by
    have he : -2 * V - (ε / 2) * ν ≤ -V - cost η ν := by
      change cost η ν ≤ V + (ε / 2) * ν at hcost
      linarith only [hcost]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)).trans (hcutoff.trans hrec)
  have hfactor : Real.exp (-(ε / 2) * ν) ≤ a / 2 := by
    have he := (div_le_iff₀ (by positivity : (0 : ℝ) < ε / 2)).mp hνlarge
    have hp : (2 / a : ℝ) ≤ Real.exp ((ε / 2) * ν) := by
      calc
        _ = Real.exp (Real.log (2 / a)) := (Real.exp_log (by positivity : (0 : ℝ) < 2 / a)).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by change Real.log (2 / a) ≤ ν * (ε / 2) at he; nlinarith only [he])
    calc
      _ = 1 / Real.exp ((ε / 2) * ν) := by rw [show -(ε / 2) * ν = -((ε / 2) * ν) by ring, Real.exp_neg, one_div]
      _ ≤ 1 / (2 / a) := one_div_le_one_div_of_le (by positivity) hp
      _ = _ := by field_simp
  calc
    _ = Real.exp (-(ε / 2) * ν) * N * Real.exp (-2 * V - (ε / 2) * ν) := by
      rw [show Real.exp (-(ε / 2) * ν) * (N : ℝ) * Real.exp (-2 * V - (ε / 2) * ν) =
        (N : ℝ) * (Real.exp (-(ε / 2) * ν) * Real.exp (-2 * V - (ε / 2) * ν)) by ring,
        ← Real.exp_add]
      congr 2
      ring
    _ ≤ (a / 2) * N * Real.exp (-2 * V - (ε / 2) * ν) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg N)) (Real.exp_nonneg _)
    _ ≤ _ := hmain

theorem lowerInput : LowerInput := uniform_lower

theorem eipInput : OrdinaryReciprocalPrimeInput.EIPInput := eipInput_of_lower lowerInput

end PaperP1.FineOrdinaryReciprocalLower
