module

public import PaperP1.Arithmetic.TwoDefectHosts
public import PaperP1.Asymptotics.UniformReal
public import PaperP1.Asymptotics.ExpSqrtLog

@[expose] public section

/-! # Uniform subpolynomial counts of starts with two defective offsets -/

namespace PaperP1.TwoDefectCount

open Finset DefectCounting TwoDefectHosts UniformQuadraticCount

theorem logarithmic_length_le_rpow_eventually
    (E : ℝ) (hE : 0 ≤ E) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ R : ℕ, (R : ℝ) ≤ E * Real.log N →
      (R + 1 : ℝ) ≤ (N : ℝ) ^ ε := by
  have hsub : UniformSubpolynomialOn
      (fun N R => (R : ℝ) ≤ E * Real.log N)
      (fun _ R => (R + 1 : ℝ)) :=
    ExpSqrtLog.uniformSubpolynomialOn_linear_log_add_one
      _ (fun _ R => R) E hE (fun _ _ h => h)
  obtain ⟨N₀, hN₀⟩ := UniformReal.uniformSubpolynomialOn_le_rpow hsub ε hε
  refine ⟨N₀, ?_⟩
  intro N hN R hR
  simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ R + 1)] using hN₀ N hN R hR

/-- Uniform T1.2 count for every actual configuration, with all coefficient
and solution heights supplied by explicit finite bounds. -/
theorem quadratic_configuration_count_eventually
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H R X : ℕ,
      4 ^ H ≤ N ^ K → X + R ≤ N ^ K →
      ∀ w ∈ configurations H R,
        ((quadraticSolutions (X + R) w).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := cardinality_le_rpow_eventually K ε hε
  refine ⟨N₀, ?_⟩
  intro N hN H R X hcoeff hheight w hw
  obtain ⟨hi, hj, hij, hS, hT⟩ := mem_configurations.mp hw
  have hApos := SmoothSupportBounds.supportProduct_pos hS
  have hCpos := SmoothSupportBounds.supportProduct_pos hT
  have he : (w.1.1 : ℤ) - (w.1.2 : ℤ) ≠ 0 := by
    intro hzero
    have heq : w.1.1 = w.1.2 := by exact_mod_cast sub_eq_zero.mp hzero
    exact hij heq
  have heR : ((w.1.1 : ℤ) - (w.1.2 : ℤ)).natAbs ≤ R := by
    have hleft : (w.1.1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hi
    have hright : (w.1.2 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hj
    have habs : |(w.1.1 : ℤ) - (w.1.2 : ℤ)| ≤ (R : ℤ) :=
      abs_le.mpr ⟨by omega, by omega⟩
    simpa only [Int.abs_eq_natAbs, Nat.cast_le] using habs
  have hRheight : R ≤ N ^ K := (show R ≤ X + R by omega).trans hheight
  exact hN₀ N hN (w.2.1.prod id) (w.2.2.prod id) (X + R)
    ((w.1.1 : ℤ) - (w.1.2 : ℤ)) hApos hCpos he
    ((SmoothSupportBounds.supportProduct_le_four_pow hS).trans hcoeff)
    ((SmoothSupportBounds.supportProduct_le_four_pow hT).trans hcoeff)
    hheight (heR.trans hRheight)

/-- Full N^o(1) bound for the actual positive starts x ≤ X whose interval
[x,x+R] contains two distinct H-defective integers. All cutoffs, widths and
counting heights follow the common threshold. -/
theorem two_defect_count_le_rpow_eventually
    (C D E : ℝ) (_hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H R X : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (R : ℝ) ≤ E * Real.log N → (X : ℝ) ≤ C * N →
      ((twoDefectStarts H R X).card : ℝ) ≤ (N : ℝ) ^ ε := by
  let δ : ℝ := ε / 5
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K : ℕ := max 2 ⌈D * Real.log 4⌉₊
  have hK2 : 2 ≤ K := le_max_left _ _
  have hKlog : D * Real.log 4 ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 ⌈D * Real.log 4⌉₊))
  obtain ⟨Nq, hq⟩ := quadratic_configuration_count_eventually K δ hδ
  obtain ⟨Ns, hs⟩ := LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually D hD δ hδ
  obtain ⟨Nr, hr⟩ := logarithmic_length_le_rpow_eventually E hE δ hδ
  refine ⟨max Nq (max Ns (max Nr (max 1 ⌈C + E⌉₊))), ?_⟩
  intro N hN H R X hH hR hX
  have hNq : Nq ≤ N := (le_max_left _ _).trans hN
  have htail : max Ns (max Nr (max 1 ⌈C + E⌉₊)) ≤ N := (le_max_right _ _).trans hN
  have hNs : Ns ≤ N := (le_max_left _ _).trans htail
  have htail' : max Nr (max 1 ⌈C + E⌉₊) ≤ N := (le_max_right _ _).trans htail
  have hNr : Nr ≤ N := (le_max_left _ _).trans htail'
  have hbasic : max 1 ⌈C + E⌉₊ ≤ N := (le_max_right _ _).trans htail'
  have hNone : 1 ≤ N := (le_max_left _ _).trans hbasic
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hCE : C + E ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 ⌈C + E⌉₊).trans hbasic)
  have hheightReal : ((X + R : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    calc
      ((X + R : ℕ) : ℝ) = (X : ℝ) + R := by push_cast; rfl
      _ ≤ C * N + E * Real.log N := add_le_add hX hR
      _ ≤ C * N + E * N :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (Real.log_le_self (Nat.cast_nonneg N)) hE)
      _ = (C + E) * N := by ring
      _ ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_right hCE (by positivity)
      _ = (N : ℝ) ^ 2 := by ring
  have hheight : X + R ≤ N ^ K :=
    (by exact_mod_cast hheightReal : X + R ≤ N ^ 2).trans
      (Nat.pow_le_pow_right hNone hK2)
  have hcoeff : 4 ^ H ≤ N ^ K :=
    SmoothSupportBounds.four_pow_cutoff_le_polynomial hNone hH hKlog
  have hquadratic := hq N hNq H R X hcoeff hheight
  have hsmooth := hs N hNs H hH
  have hwidth := hr N hNr R hR
  calc
    _ ≤ (R + 1 : ℝ) ^ 2 * ((smallPrimesUpTo H).powerset.card : ℝ) ^ 2 *
        (N : ℝ) ^ δ :=
      card_twoDefectStarts_le_box_bound (by positivity) hquadratic
    _ ≤ ((N : ℝ) ^ δ) ^ 2 * ((N : ℝ) ^ δ) ^ 2 * (N : ℝ) ^ δ := by
      gcongr
    _ = (N : ℝ) ^ ε := by
      simp only [pow_two]
      simp only [← Real.rpow_add hNpos]
      congr 1
      dsimp [δ]
      ring

end PaperP1.TwoDefectCount

