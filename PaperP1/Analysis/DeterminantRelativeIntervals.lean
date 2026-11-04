module

public import PaperP1.Arithmetic.ActualRelativeDeterminant
public import Mathlib.Algebra.Order.Floor.Semifield

/-! # Actual finite relative intervals cover every point in a dyadic ratio box -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantRelativeIntervals

open Finset

def scaledRatio (M : ℕ) (D E d e : ℝ) : ℝ := (M : ℝ) * ((d / e) / (D / E))
def intervalIndex (M : ℕ) (D E d e : ℝ) : ℕ := ⌊scaledRatio M D E d e⌋₊
def intervalCenter (M : ℕ) (D E : ℝ) (k : ℕ) : ℝ := (D / E) * (k : ℝ) / M
def intervalIndices (M : ℕ) : Finset ℕ := Icc 1 (2 * M)

theorem ratio_bounds {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    (1 / 2 : ℝ) ≤ (d / e) / (D / E) ∧ (d / e) / (D / E) ≤ 2 := by
  have he : 0 < e := hE.trans_le helo
  have hbase : 0 < D / E := div_pos hD hE
  constructor
  · apply (le_div_iff₀ hbase).mpr
    have hlo : D / (2 * E) ≤ d / e := by
      apply (div_le_div_iff₀ (by positivity) he).mpr
      have h₁ := mul_le_mul_of_nonneg_left hehi hD.le
      have h₂ := mul_le_mul_of_nonneg_right hdlo (show 0 ≤ 2 * E by positivity)
      nlinarith only [h₁, h₂]
    convert hlo using 1
    ring
  · apply (div_le_iff₀ hbase).mpr
    have hhi : d / e ≤ 2 * D / E := by
      apply (div_le_div_iff₀ he hE).mpr
      have h₁ := mul_le_mul_of_nonneg_right hdhi hE.le
      have h₂ := mul_le_mul_of_nonneg_left helo (show 0 ≤ 2 * D by positivity)
      nlinarith only [h₁, h₂]
    convert hhi using 1
    ring

theorem scaled_bounds (M : ℕ) {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    (M : ℝ) / 2 ≤ scaledRatio M D E d e ∧ scaledRatio M D E d e ≤ 2 * M := by
  have h := ratio_bounds hD hE hdlo hdhi helo hehi
  constructor
  · simpa only [scaledRatio, mul_one_div] using mul_le_mul_of_nonneg_left h.1 (Nat.cast_nonneg M)
  · simpa only [scaledRatio, mul_comm] using mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg M)

theorem index_bounds (M : ℕ) (hM : 4 ≤ M) {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    (M : ℝ) / 4 ≤ intervalIndex M D E d e ∧ intervalIndex M D E d e ≤ 2 * M := by
  have h := scaled_bounds M hD hE hdlo hdhi helo hehi
  have hMR : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : 0 ≤ scaledRatio M D E d e := by linarith only [h.1, hMR]
  have hfloor := Nat.lt_floor_add_one (scaledRatio M D E d e)
  have hle := Nat.floor_le hx
  constructor
  · change (M : ℝ) / 4 ≤ (⌊scaledRatio M D E d e⌋₊ : ℝ)
    linarith only [h.1, hMR, hfloor]
  · apply (Nat.cast_le (α := ℝ)).mp
    simpa only [Nat.cast_mul, Nat.cast_ofNat, intervalIndex] using hle.trans h.2

theorem index_mem (M : ℕ) (hM : 4 ≤ M) {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    intervalIndex M D E d e ∈ intervalIndices M := by
  have h := index_bounds M hM hD hE hdlo hdhi helo hehi
  have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hk : (1 : ℝ) ≤ intervalIndex M D E d e := by linarith only [h.1, hm]
  exact mem_Icc.mpr ⟨by exact_mod_cast hk, h.2⟩

theorem center_bounds (M : ℕ) (hM : 4 ≤ M) {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    D / (4 * E) ≤ intervalCenter M D E (intervalIndex M D E d e) ∧
      intervalCenter M D E (intervalIndex M D E d e) ≤ 2 * D / E := by
  have hk := index_bounds M hM hD hE hdlo hdhi helo hehi
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlo := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hk.1 (div_pos hD hE).le) hMp.le
  have hhi := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show (intervalIndex M D E d e : ℝ) ≤ 2 * M by exact_mod_cast hk.2)
      (div_pos hD hE).le) hMp.le
  constructor
  · change D / (4 * E) ≤ (D / E) * (intervalIndex M D E d e : ℝ) / M
    convert hlo using 1
    field_simp
  · change (D / E) * (intervalIndex M D E d e : ℝ) / M ≤ 2 * D / E
    convert hhi using 1
    field_simp

theorem intervalIndices_card (M : ℕ) : (intervalIndices M).card = 2 * M := by
  simp only [intervalIndices, Nat.card_Icc, Nat.add_sub_cancel]

theorem alpha_identity (M k : ℕ) (hM : 0 < M) (hk : 0 < k)
    {D E d e : ℝ} (hD : 0 < D) (he : 0 < e) :
    DeterminantRelativeChart.alpha d e (intervalCenter M D E k) =
      (scaledRatio M D E d e - k) / k := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold DeterminantRelativeChart.alpha intervalCenter scaledRatio
  field_simp

theorem alpha_bounds (M : ℕ) (hM : 4 ≤ M) {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    0 ≤ DeterminantRelativeChart.alpha d e (intervalCenter M D E (intervalIndex M D E d e)) ∧
      DeterminantRelativeChart.alpha d e (intervalCenter M D E (intervalIndex M D E d e)) ≤ 4 / M := by
  have hscaled := scaled_bounds M hD hE hdlo hdhi helo hehi
  have hk := index_bounds M hM hD hE hdlo hdhi helo hehi
  have hkN : 0 < intervalIndex M D E d e := (mem_Icc.mp (index_mem M hM hD hE hdlo hdhi helo hehi)).1
  have hkR : (0 : ℝ) < intervalIndex M D E d e := by exact_mod_cast hkN
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hx : 0 ≤ scaledRatio M D E d e := by linarith only [hscaled.1, hMR]
  have hfloor := Nat.floor_le hx
  have hlt := Nat.lt_floor_add_one (scaledRatio M D E d e)
  rw [alpha_identity M _ (by omega) hkN hD (hE.trans_le helo)]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hfloor) hkR.le
  · calc
      _ ≤ 1 / (intervalIndex M D E d e : ℝ) := by
        apply div_le_div_of_nonneg_right _ hkR.le
        change scaledRatio M D E d e - (⌊scaledRatio M D E d e⌋₊ : ℝ) ≤ 1
        linarith only [hlt]
      _ ≤ 4 / M := by
        apply (div_le_div_iff₀ hkR hMR).mpr
        nlinarith only [hk.1]

theorem alpha_absolute_bound (M : ℕ) (hM : 4 ≤ M) {D E d e : ℝ} (hD : 0 < D) (hE : 0 < E)
    (hdlo : D ≤ d) (hdhi : d ≤ 2 * D) (helo : E ≤ e) (hehi : e ≤ 2 * E) :
    |DeterminantRelativeChart.alpha d e (intervalCenter M D E (intervalIndex M D E d e))| ≤ 4 / M := by
  have h := alpha_bounds M hM hD hE hdlo hdhi helo hehi
  simpa only [abs_of_nonneg h.1] using h.2

end PaperP1.DeterminantRelativeIntervals
