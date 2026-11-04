module

public import PaperP1.Arithmetic.ActualSourcePrimitiveReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Normalize reduced dyadic scales using the actual positive integer points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedDyadicScales

def enlarged (D : ℝ) (g : ℕ) : ℝ := max 1 (D / g)

theorem enlarged_ge_one (D : ℝ) (g : ℕ) : 1 ≤ enlarged D g := le_max_left _ _

theorem raw_le_enlarged (D : ℝ) (g : ℕ) : D / g ≤ enlarged D g := le_max_right _ _

theorem enlarged_le_double (D : ℝ) (g : ℕ) (hD : 1 / 2 ≤ D / g) : enlarged D g ≤ 2 * (D / g) := by
  apply max_le
  · linarith
  · linarith

theorem integer_point_bounds (D : ℝ) (g m : ℕ) (hm : 0 < m)
    (hlo : D / g ≤ (m : ℝ)) (hhi : (m : ℝ) ≤ 2 * (D / g)) :
    enlarged D g ≤ m ∧ (m : ℝ) ≤ 2 * enlarged D g ∧ 1 / 2 ≤ D / g ∧ enlarged D g ≤ 2 * (D / g) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hhalf : 1 / 2 ≤ D / g := by linarith
  exact ⟨max_le hmR hlo, hhi.trans (by linarith [raw_le_enlarged D g]), hhalf, enlarged_le_double D g hhalf⟩

theorem source_product_lower (c D U : ℝ) (g q : ℕ) (hc : 0 ≤ c) (hD : 0 ≤ D) (hU : 0 ≤ U) :
    c * (D / g) ^ 2 * (U / q) ≤ c * enlarged D g ^ 2 * enlarged U q := by
  have hd : 0 ≤ D / g := div_nonneg hD (Nat.cast_nonneg g)
  have hu : 0 ≤ U / q := div_nonneg hU (Nat.cast_nonneg q)
  gcongr
  · exact raw_le_enlarged D g
  · exact raw_le_enlarged U q

theorem source_product_upper (c D U : ℝ) (g q : ℕ) (hc : 0 ≤ c)
    (hD : 1 / 2 ≤ D / g) (hU : 1 / 2 ≤ U / q) :
    c * enlarged D g ^ 2 * enlarged U q ≤ 8 * (c * (D / g) ^ 2 * (U / q)) := by
  have hd : 0 ≤ enlarged D g := (by norm_num : (0 : ℝ) ≤ 1).trans (enlarged_ge_one D g)
  have hu : 0 ≤ enlarged U q := (by norm_num : (0 : ℝ) ≤ 1).trans (enlarged_ge_one U q)
  calc
    _ ≤ c * (2 * (D / g)) ^ 2 * (2 * (U / q)) := by
      gcongr
      · exact enlarged_le_double D g hD
      · exact enlarged_le_double U q hU
    _ = _ := by ring

theorem raw_log_product (D E : ℝ) (g : ℕ) (hD : 0 < D) (hE : 0 < E) (hg : 0 < g) :
    Real.log ((D / g) * (E / g)) = Real.log (D * E) - 2 * Real.log g := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  rw [Real.log_mul (div_pos hD hgR).ne' (div_pos hE hgR).ne',
    Real.log_div hD.ne' hgR.ne', Real.log_div hE.ne' hgR.ne', Real.log_mul hD.ne' hE.ne']
  ring

theorem log_product_lower (D E : ℝ) (g : ℕ) (hD : 0 < D) (hE : 0 < E) (hg : 0 < g) :
    Real.log (D * E) - 2 * Real.log g ≤ Real.log (enlarged D g * enlarged E g) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hd : 0 < D / g := div_pos hD hgR
  have he : 0 < E / g := div_pos hE hgR
  have hup : (D / g) * (E / g) ≤ enlarged D g * enlarged E g :=
    mul_le_mul (raw_le_enlarged D g) (raw_le_enlarged E g) he.le (hd.le.trans (raw_le_enlarged D g))
  have ht := Real.log_le_log (mul_pos hd he) hup
  simpa only [raw_log_product D E g hD hE hg] using ht

theorem log_product_upper (D E : ℝ) (g : ℕ) (hD : 0 < D) (hE : 0 < E) (hg : 0 < g)
    (hhalfD : 1 / 2 ≤ D / g) (hhalfE : 1 / 2 ≤ E / g) :
    Real.log (enlarged D g * enlarged E g) ≤ Real.log (D * E) - 2 * Real.log g + Real.log 4 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hd : 0 < enlarged D g := lt_of_lt_of_le (by norm_num) (enlarged_ge_one D g)
  have he : 0 < enlarged E g := lt_of_lt_of_le (by norm_num) (enlarged_ge_one E g)
  have hup : enlarged D g * enlarged E g ≤ 4 * ((D / g) * (E / g)) := by
    calc
      _ ≤ (2 * (D / g)) * (2 * (E / g)) :=
        mul_le_mul (enlarged_le_double D g hhalfD) (enlarged_le_double E g hhalfE) he.le (by linarith)
      _ = _ := by ring
  have ht := Real.log_le_log (mul_pos hd he) hup
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (mul_pos (div_pos hD hgR) (div_pos hE hgR)).ne',
    raw_log_product D E g hD hE hg] at ht
  linarith

end PaperP1.ReducedDyadicScales
