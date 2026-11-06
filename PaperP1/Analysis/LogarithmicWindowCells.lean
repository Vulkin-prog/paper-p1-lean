module

public import PaperP1.Analysis.GaussianFrequencyRowBound


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicWindowCells
open MeasureTheory PaperP1
open scoped Classical

def cell (c : ℝ) (j : ℕ) : Set ℝ :=
  Set.Ioc (-Real.log ((j : ℝ)+c+1)) (-Real.log ((j : ℝ)+c))

theorem log_ratio_upper (M x y : ℝ) (hM : 0 < M) (hx : M ≤ x) (hy : M ≤ y) :
    |Real.log (y/x)| ≤ |y-x|/M := by
  have hxP : 0 < x := hM.trans_le hx
  have hyP : 0 < y := hM.trans_le hy
  rcases le_total y x with hyx | hxy
  · have hNonpos : Real.log (y/x) ≤ 0 :=
      Real.log_nonpos (div_nonneg hyP.le hxP.le) ((div_le_one hxP).mpr hyx)
    have hLog : -Real.log (y/x)=Real.log (x/y) := by
      rw [Real.log_div hyP.ne' hxP.ne',Real.log_div hxP.ne' hyP.ne']
      ring
    rw [abs_of_nonpos hNonpos,hLog,abs_of_nonpos (sub_nonpos.mpr hyx)]
    calc
      _ ≤ x/y-1 := Real.log_le_sub_one_of_pos (div_pos hxP hyP)
      _ = (x-y)/y := by field_simp
      _ ≤ (x-y)/M := div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hM hy
      _ = _ := by ring
  · have hNonneg : 0 ≤ Real.log (y/x) := Real.log_nonneg ((one_le_div hxP).mpr hxy)
    rw [abs_of_nonneg hNonneg,abs_of_nonneg (sub_nonneg.mpr hxy)]
    calc
      _ ≤ y/x-1 := Real.log_le_sub_one_of_pos (div_pos hyP hxP)
      _ = (y-x)/x := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hM hx

theorem log_ratio_lower (M x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M) :
    |y-x|/M ≤ |Real.log (y/x)| := by
  rw [Real.log_div hy.ne' hx.ne']
  exact GaussianFrequencyRowBound.absolute_log_gap x y M hx hy hxM hyM

theorem outside_window_gap (j h n : ℕ) (hh : 6 ≤ h) (x : ℝ)
    (hxL : (j : ℝ)+(h : ℝ)/2 ≤ x) (hxR : x ≤ (j : ℝ)+(h : ℝ)/2+1)
    (hn : n ∉ Finset.Ico j (j+h)) : (h : ℝ)/3 ≤ |(n : ℝ)-x| := by
  have hhR : (6 : ℝ) ≤ h := by exact_mod_cast hh
  by_cases hnj : n < j
  · have hnR : (n : ℝ) < j := by exact_mod_cast hnj
    rw [abs_of_nonpos (by linarith only [hnR,hxL,hhR] : (n : ℝ)-x ≤ 0)]
    linarith only [hnR,hxL,hhR]
  · have hnEnd : j+h ≤ n := by simp only [Finset.mem_Ico] at hn; omega
    have hnR : (j : ℝ)+(h : ℝ) ≤ n := by exact_mod_cast hnEnd
    rw [abs_of_nonneg (by linarith only [hnR,hxR,hhR] : 0 ≤ (n : ℝ)-x)]
    linarith only [hnR,hxR,hhR]

theorem cell_measurable (c : ℝ) (j : ℕ) : MeasurableSet (cell c j) := measurableSet_Ioc

theorem cell_measure_lower (c M : ℝ) (j : ℕ) (hX : 0 < (j : ℝ)+c)
    (hTop : (j : ℝ)+c+1 ≤ M) : 1/M ≤ volume.real (cell c j) := by
  have hh := GaussianFrequencyRowBound.ordered_log_gap ((j : ℝ)+c) ((j : ℝ)+c+1) M
    hX (by linarith only [hX]) hTop (by linarith)
  have hGap : 1/M ≤ Real.log ((j : ℝ)+c+1)-Real.log ((j : ℝ)+c) := by
    simpa only [add_sub_cancel_left] using hh
  rw [cell,Real.volume_real_Ioc]
  calc
    _ ≤ Real.log ((j : ℝ)+c+1)-Real.log ((j : ℝ)+c) := hGap
    _ = -Real.log ((j : ℝ)+c)-(-Real.log ((j : ℝ)+c+1)) := by ring
    _ ≤ _ := le_max_left _ _

theorem cells_disjoint (c : ℝ) (i j : ℕ) (hi : 0 < (i : ℝ)+c) (hj : 0 < (j : ℝ)+c)
    (hij : i≠j) : Disjoint (cell c i) (cell c j) := by
  wlog hlt : i<j generalizing i j
  · exact (this j i hj hi hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hlt) hij.symm)).symm
  have hTop : (i : ℝ)+c+1 ≤ (j : ℝ)+c := by
    have hh : (i : ℝ)+1 ≤ j := by exact_mod_cast hlt
    linarith only [hh]
  have hLog := Real.log_le_log (by linarith only [hi] : 0 < (i : ℝ)+c+1) hTop
  apply Set.disjoint_left.mpr
  intro u huI huJ
  have hIL := (Set.mem_Ioc.mp huI).1
  have hJR := (Set.mem_Ioc.mp huJ).2
  linarith only [hLog,hIL,hJR]

end PaperP1.LogarithmicWindowCells
