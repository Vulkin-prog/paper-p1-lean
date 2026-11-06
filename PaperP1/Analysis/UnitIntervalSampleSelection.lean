module

public import PaperP1.Analysis.FiniteFrequencyCover

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UnitIntervalSampleSelection
open Finset MeasureTheory PaperP1
open scoped Classical

def cell (a : ℝ) (i : ℕ) : Set ℝ := Set.Icc (a+(i : ℝ)) (a+(i : ℝ)+1)

theorem cell_volume (a : ℝ) (i : ℕ) : volume.real (cell a i)=1 := by
  rw [cell,Real.volume_real_Icc]
  simp

theorem cell_cover (T t : ℝ) (ht : t ∈ Set.Ioc (-T) T) :
    ∃ i ∈ range (⌈2*T⌉₊+1), t ∈ cell (-T) i := by
  let i := ⌊t+T⌋₊
  have h0 : 0 ≤ t+T := by linarith only [ht.1]
  have hlo : (i : ℝ) ≤ t+T := Nat.floor_le h0
  have hhi := Nat.lt_floor_add_one (t+T)
  have hceil := Nat.le_ceil (2*T)
  have hIndex : i ≤ ⌈2*T⌉₊ := by
    have hh : (i : ℝ) ≤ (⌈2*T⌉₊ : ℝ) := by linarith only [hlo,ht.2,hceil]
    exact_mod_cast hh
  refine ⟨i,mem_range.mpr (by omega),?_⟩
  change -T+(i : ℝ) ≤ t ∧ t ≤ -T+(i : ℝ)+1
  change t+T < (i : ℝ)+1 at hhi
  constructor <;> linarith only [hlo,hhi]

theorem cell_separated (a s t : ℝ) (i j : ℕ) (hi : s ∈ cell a i) (hj : t ∈ cell a j)
    (hParity : i%2=j%2) (hne : i ≠ j) : 1 ≤ |s-t| := by
  rcases (show i+2 ≤ j ∨ j+2 ≤ i by omega) with h | h
  · have hh : (i : ℝ)+2 ≤ j := by exact_mod_cast h
    have hdiff : s-t ≤ 0 := by linarith only [hi.2,hj.1,hh]
    rw [abs_of_nonpos hdiff]
    linarith only [hi.2,hj.1,hh]
  · have hh : (j : ℝ)+2 ≤ i := by exact_mod_cast h
    have hdiff : 0 ≤ s-t := by linarith only [hi.1,hj.2,hh]
    rw [abs_of_nonneg hdiff]
    linarith only [hi.1,hj.2,hh]

theorem exists_sample (a : ℝ) (i : ℕ) (E : Set ℝ) (hE : E ⊆ cell a i)
    (hne : E.Nonempty) (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ g t) :
    ∃ t ∈ E, (∫ x in E, g x) ≤ 2*g t := by
  let I := ∫ x in E, g x
  by_cases hI : I ≤ 0
  · obtain ⟨t,ht⟩ := hne
    exact ⟨t,ht,hI.trans (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hg t))⟩
  have hIp : 0 < I := lt_of_not_ge hI
  by_contra hnot
  push Not at hnot
  have hμ : volume E < ⊤ := (measure_mono hE).trans_lt isCompact_Icc.measure_lt_top
  have hμReal : volume.real E ≤ 1 := by
    have hh := measureReal_mono (μ := volume) hE isCompact_Icc.measure_ne_top
    rw [cell_volume] at hh
    exact hh
  have hNorm : ∀ t ∈ E, ‖g t‖ ≤ I/2 := by
    intro t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (hg t)]
    have hh := hnot t ht
    linarith only [hh]
  have hBound := norm_setIntegral_le_of_norm_le_const (μ := volume) hμ hNorm
  change ‖I‖ ≤ (I/2)*volume.real E at hBound
  rw [Real.norm_eq_abs,abs_of_pos hIp] at hBound
  have hh := mul_le_mul_of_nonneg_left hμReal (show 0 ≤ I/2 by positivity)
  nlinarith only [hBound,hh,hIp]
end PaperP1.UnitIntervalSampleSelection
