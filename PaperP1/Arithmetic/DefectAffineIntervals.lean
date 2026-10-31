module

public import PaperP1.Coding.LocalDefectWindowScale
public import PaperP1.Arithmetic.GlobalDefectCount
public import PaperP1.Arithmetic.TwoDefectCount

@[expose] public section

/-! # Fixed real affine changes of integer intervals -/

namespace PaperP1.DefectAffineIntervals

open Finset DefectivePredicate LocalDefectBound

noncomputable def affineBase (a b : ℝ) (U : ℕ) : ℕ := ⌈a * U + b⌉₊

noncomputable def affineWidth (a : ℝ) (R : ℕ) : ℕ := ⌈a * R⌉₊

noncomputable def affineHeight (a b : ℝ) (X : ℕ) : ℕ := ⌊a * X + b⌋₊

/-- Actual positive defective integer points in the real interval
[aU+b, a(U+R)+b], represented by exact integer endpoints. -/
noncomputable def affineIntervalDefects (a b : ℝ) (H U R : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 (affineHeight a b (U + R))).filter fun n =>
    a * U + b ≤ (n : ℝ) ∧ (n : ℝ) ≤ a * ((U + R : ℕ) : ℝ) + b ∧ HDefective H n

theorem mem_affineIntervalDefects {a b : ℝ} {H U R n : ℕ} :
    n ∈ affineIntervalDefects a b H U R ↔
      0 < n ∧ a * U + b ≤ (n : ℝ) ∧
        (n : ℝ) ≤ a * ((U + R : ℕ) : ℝ) + b ∧ HDefective H n := by
  classical
  simp only [affineIntervalDefects, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hn1, _hnUpper⟩, hnlo, hnhi, hdef⟩
    exact ⟨by omega, hnlo, hnhi, hdef⟩
  · rintro ⟨hnpos, hnlo, hnhi, hdef⟩
    exact ⟨⟨by omega, Nat.le_floor hnhi⟩, hnlo, hnhi, hdef⟩

theorem affineWidth_le_add_one {a : ℝ} (ha : 0 ≤ a) (R : ℕ) :
    (affineWidth a R : ℝ) ≤ a * R + 1 :=
  (Nat.ceil_lt_add_one (mul_nonneg ha (Nat.cast_nonneg R))).le

theorem affineHeight_le_linear
    {a b C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    {N X : ℕ} (hN : 1 ≤ N) (hX : (X : ℝ) ≤ C * N) :
    (affineHeight a b X : ℝ) ≤ (a * C + |b| + 1) * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hraw : a * X + b ≤ (a * C + |b| + 1) * N := by
    have hmul := mul_le_mul_of_nonneg_left hX ha
    have hbmul : |b| ≤ |b| * N := by nlinarith [abs_nonneg b]
    nlinarith [le_abs_self b]
  by_cases hnonneg : 0 ≤ a * X + b
  · exact (Nat.floor_le hnonneg).trans hraw
  · have hfloor : affineHeight a b X = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hfloor]
    simp only [Nat.cast_zero]
    positivity

theorem affineWidth_le_log
    {a E : ℝ} (ha : 0 ≤ a) {N R : ℕ}
    (hlog : 1 ≤ Real.log (N : ℝ)) (hR : (R : ℝ) ≤ E * Real.log N) :
    (affineWidth a R : ℝ) ≤ (a * E + 1) * Real.log N := by
  calc
    _ ≤ a * R + 1 := affineWidth_le_add_one ha R
    _ ≤ a * (E * Real.log N) + Real.log N :=
      add_le_add (mul_le_mul_of_nonneg_left hR ha) hlog
    _ = _ := by ring

theorem affineWidth_le_window
    {a Rscale B : ℝ} (ha : 0 ≤ a) {R : ℕ}
    (hB : 1 ≤ B) (hR : (R : ℝ) ≤ Rscale * B) :
    (affineWidth a R : ℝ) ≤ (a * Rscale + 1) * B := by
  calc
    _ ≤ a * R + 1 := affineWidth_le_add_one ha R
    _ ≤ a * (Rscale * B) + B :=
      add_le_add (mul_le_mul_of_nonneg_left hR ha) hB
    _ = _ := by ring

theorem affineBase_bounds
    {a b c C : ℝ} (ha : 0 < a) (hc : 0 < c) (_hC : 0 < C)
    {N U : ℕ} (hN : 1 ≤ N)
    (hshift : 2 * |b| / (a * c) ≤ (N : ℝ))
    (hUlo : c * N ≤ (U : ℝ)) (hUhi : (U : ℝ) ≤ C * N) :
    0 ≤ a * U + b ∧
      (a * c / 2) * N ≤ (affineBase a b U : ℝ) ∧
        (affineBase a b U : ℝ) ≤ (a * C + |b| + 1) * N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hshiftMul : 2 * |b| ≤ (a * c) * N := by
    have h := (div_le_iff₀ (mul_pos ha hc)).mp hshift
    nlinarith
  have hleft : (a * c / 2) * N ≤ a * U + b := by
    have hmul := mul_le_mul_of_nonneg_left hUlo ha.le
    nlinarith [neg_le_abs b]
  have hleftpos : 0 < (a * c / 2) * N := by positivity
  have hnonneg : 0 ≤ a * U + b := (hleftpos.trans_le hleft).le
  have hceil : a * U + b ≤ (affineBase a b U : ℝ) := Nat.le_ceil _
  have hupper : (affineBase a b U : ℝ) ≤ (a * C + |b| + 1) * N := by
    have hceilUp : (affineBase a b U : ℝ) < a * U + b + 1 :=
      Nat.ceil_lt_add_one hnonneg
    have hmul := mul_le_mul_of_nonneg_left hUhi ha.le
    have hbmul : |b| ≤ |b| * N := by nlinarith [abs_nonneg b]
    nlinarith [le_abs_self b]
  exact ⟨hnonneg, hleft.trans hceil, hupper⟩

theorem affineIntervalDefects_subset
    {a b : ℝ} {H U R : ℕ} :
    affineIntervalDefects a b H U R ⊆
      defectsInInterval H (affineBase a b U) (affineWidth a R) := by
  classical
  intro n hn
  obtain ⟨_hnpos, hnlo, hnhi, hdef⟩ := mem_affineIntervalDefects.mp hn
  have hlo : affineBase a b U ≤ n := Nat.ceil_le.mpr hnlo
  have hceil : a * U + b ≤ (affineBase a b U : ℝ) := Nat.le_ceil _
  have hwidth : a * R ≤ (affineWidth a R : ℝ) := Nat.le_ceil _
  have hnupper : n ≤ affineBase a b U + affineWidth a R := by
    have hbound : (n : ℝ) ≤ (affineBase a b U : ℝ) + affineWidth a R := by
      push_cast at hnhi
      nlinarith
    exact_mod_cast hbound
  exact mem_defectsInInterval.mpr ⟨hlo, hnupper, hdef⟩

end PaperP1.DefectAffineIntervals

