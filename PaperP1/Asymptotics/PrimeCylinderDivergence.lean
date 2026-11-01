module

public import PaperP1.Asymptotics.PrimeCylinderScale

/-! # Divergence of the original positive and total run exponential moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCylinderDivergence

open Filter PaperP1.Model PaperP1.PrimeCylinderScale PaperP1.LocalDefectBound

def scale (q : ℕ) : ℝ := Real.log (size q) / size q

def startLower (q : ℕ) : ℝ :=
  scale q * ((size q : ℝ) / q - 2 * size q / (q : ℝ) ^ 2 - 4)

def lowerRate (t : ℝ) (q : ℕ) : ℝ := t * startLower q - primeCharge q

def positiveRate (t : ℝ) (q : ℕ) : ℝ :=
  scale q * Real.log (PositiveStarts.exponentialMoment (dyadicBlock (size q)) (q - 1) t)

def totalRate (t : ℝ) (q : ℕ) : ℝ :=
  scale q * Real.log (PrimeRunCylinder.totalExponentialMoment (size q) (q - 1) t)

theorem scale_nonneg (q : ℕ) : 0 ≤ scale q := by
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast size_pos q)
  · exact_mod_cast (size_pos q).le

theorem scale_pos {q : ℕ} (hq : 2 ≤ q) : 0 < scale q := by
  apply div_pos
  · exact Real.log_pos (by exact_mod_cast (show 1 < size q by have h := index_le_size (by omega : 1 ≤ q); omega))
  · exact_mod_cast size_pos q

theorem scale_tendsto_zero : Tendsto scale atTop (nhds 0) := log_size_div_size_tendsto

theorem startLower_tendsto : Tendsto startLower atTop (nhds (Real.log 2)) := by
  have hinv : Tendsto (fun q : ℕ ↦ (1 : ℝ) / q) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfactor : Tendsto (fun q : ℕ ↦ 1 - 2 * (1 / (q : ℝ))) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub (hinv.const_mul 2)
  have heq : startLower =ᶠ[atTop] (fun q : ℕ ↦
      (Real.log (size q) / q) * (1 - 2 * (1 / (q : ℝ))) - 4 * scale q) := by
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hN : (size q : ℝ) ≠ 0 := by exact_mod_cast (size_pos q).ne'
    unfold startLower scale
    field_simp
  exact Tendsto.congr' heq.symm (by simpa using
    (log_size_div_index_tendsto.mul hfactor).sub (scale_tendsto_zero.const_mul 4))

theorem lowerRate_tendsto (t : ℝ) :
    Tendsto (lowerRate t) atTop (nhds ((t - 2) * Real.log 2)) := by
  change Tendsto (fun q ↦ t * startLower q - primeCharge q) atTop (nhds ((t - 2) * Real.log 2))
  have h := (startLower_tendsto.const_mul t).sub primeCharge_tendsto
  have heq : t * Real.log 2 - 2 * Real.log 2 = (t - 2) * Real.log 2 := by ring
  simpa only [lowerRate, heq] using h

theorem lowerRate_le_positive {q : ℕ} (hq : Nat.Prime q) (t : ℝ) (ht : 0 ≤ t) :
    lowerRate t q ≤ positiveRate t q := by
  have hqN := index_le_size (by have h := hq.two_le; omega : 1 ≤ q)
  have hcount := PrimeRunStarts.starts_card_lower hq.two_le hqN
  have hlog := PrimeRunCylinder.positive_log_lower hq hqN t ht
  have hmul := mul_le_mul_of_nonneg_left
    ((sub_le_sub_right (mul_le_mul_of_nonneg_left hcount ht) _).trans hlog) (scale_nonneg q)
  simpa only [lowerRate, startLower, primeCharge, positiveRate, cutoff, scale, mul_sub, mul_assoc, mul_left_comm] using hmul

theorem lowerRate_le_total {q : ℕ} (hq : Nat.Prime q) (t : ℝ) (ht : 0 ≤ t) :
    lowerRate t q ≤ totalRate t q := by
  have hqN := index_le_size (by have h := hq.two_le; omega : 1 ≤ q)
  have hcount := PrimeRunStarts.starts_card_lower hq.two_le hqN
  have hlog := PrimeRunCylinder.total_log_lower hq hqN t ht
  have hmul := mul_le_mul_of_nonneg_left
    ((sub_le_sub_right (mul_le_mul_of_nonneg_left hcount ht) _).trans hlog) (scale_nonneg q)
  simpa only [lowerRate, startLower, primeCharge, totalRate, cutoff, scale, mul_sub, mul_assoc, mul_left_comm] using hmul

theorem threshold_positive {t : ℝ} (ht : 2 < t) : 0 < (t - 2) * Real.log 2 :=
  mul_pos (sub_pos.mpr ht) (Real.log_pos (by norm_num))

/-- The liminf lower bound, expressed with all thresholds and prime indices explicit. -/
theorem companion_T19_7 (t : ℝ) (ht : 2 < t) :
    0 < (t - 2) * Real.log 2 ∧
      ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, 3 ≤ q₀ ∧ ∀ q : ℕ, q₀ ≤ q → Nat.Prime q →
        (t - 2) * Real.log 2 - ε ≤ positiveRate t q ∧
        (t - 2) * Real.log 2 - ε ≤ totalRate t q := by
  refine ⟨threshold_positive ht, fun ε hε ↦ ?_⟩
  have hevent := (lowerRate_tendsto t).eventually
    (eventually_gt_nhds (by linarith : (t - 2) * Real.log 2 - ε < (t - 2) * Real.log 2))
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp hevent
  refine ⟨max q₀ 3, le_max_right _ _, fun q hq hprime ↦ ?_⟩
  have hlow := (hq₀ q (by omega)).le
  exact ⟨hlow.trans (lowerRate_le_positive hprime t (by linarith)),
    hlow.trans (lowerRate_le_total hprime t (by linarith))⟩

theorem logarithms_diverge (t : ℝ) (ht : 2 < t) (B : ℝ) :
    ∃ q₀ : ℕ, 3 ≤ q₀ ∧ ∀ q : ℕ, q₀ ≤ q → Nat.Prime q →
      B ≤ Real.log (PositiveStarts.exponentialMoment (dyadicBlock (size q)) (q - 1) t) ∧
      B ≤ Real.log (PrimeRunCylinder.totalExponentialMoment (size q) (q - 1) t) := by
  have hC := threshold_positive ht
  have hlow := (lowerRate_tendsto t).eventually
    (eventually_gt_nhds (by linarith : (t - 2) * Real.log 2 / 2 < (t - 2) * Real.log 2))
  have hsmall := (scale_tendsto_zero.const_mul B).eventually
    (eventually_lt_nhds (by linarith : B * 0 < (t - 2) * Real.log 2 / 2))
  obtain ⟨q₀, hq₀⟩ := eventually_atTop.mp (hlow.and hsmall)
  refine ⟨max q₀ 3, le_max_right _ _, fun q hq hprime ↦ ?_⟩
  obtain ⟨hrate, hB⟩ := hq₀ q (by omega)
  have hs := scale_pos (by omega : 2 ≤ q)
  have hpos := lowerRate_le_positive hprime t (by linarith)
  have htotal := lowerRate_le_total hprime t (by linarith)
  unfold positiveRate at hpos
  unfold totalRate at htotal
  constructor <;> nlinarith

theorem moments_diverge (t : ℝ) (ht : 2 < t) (K : ℝ) :
    ∃ q₀ : ℕ, 3 ≤ q₀ ∧ ∀ q : ℕ, q₀ ≤ q → Nat.Prime q →
      K ≤ PositiveStarts.exponentialMoment (dyadicBlock (size q)) (q - 1) t ∧
      K ≤ PrimeRunCylinder.totalExponentialMoment (size q) (q - 1) t := by
  obtain ⟨q₀, hq₀, hbound⟩ := logarithms_diverge t ht (Real.log (max K 1))
  refine ⟨q₀, hq₀, fun q hq hprime ↦ ?_⟩
  obtain ⟨hpos, htotal⟩ := hbound q hq hprime
  have hqN := index_le_size (by omega : 1 ≤ q)
  have hexp := PrimeRunCylinder.positive_exponential_lower hprime hqN t (by linarith)
  have hpos0 := (Real.exp_pos _).trans_le hexp
  have htotal0 := hpos0.trans_le (PrimeRunCylinder.positive_le_total (size q) (q - 1) t (by linarith))
  constructor
  · have h := Real.exp_le_exp.mpr hpos
    rw [Real.exp_log (by have h := le_max_right K 1; linarith), Real.exp_log hpos0] at h
    exact (le_max_left K 1).trans h
  · have h := Real.exp_le_exp.mpr htotal
    rw [Real.exp_log (by have h := le_max_right K 1; linarith), Real.exp_log htotal0] at h
    exact (le_max_left K 1).trans h

end PaperP1.PrimeCylinderDivergence
