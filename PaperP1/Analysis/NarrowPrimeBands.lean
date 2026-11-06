module

public import PaperP1.Analysis.DyadicLogBands

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowPrimeBands
open Finset PaperP1
open scoped Classical

def index (H p : ℕ) : ℕ := ⌊(H : ℝ)*Real.log (p : ℝ)⌋₊

def anchor (H j : ℕ) : ℝ := Real.exp ((j : ℝ)/(H : ℝ))

def growth (H : ℕ) : ℝ := Real.exp (1/(H : ℝ))

def band (H : ℕ) (P : Finset ℕ) (j : ℕ) : Finset ℕ := P.filter (fun p ↦ index H p=j)

def indices (H : ℕ) (P : Finset ℕ) : Finset ℕ := P.image (index H)

theorem anchor_pos (H j : ℕ) : 0 < anchor H j := Real.exp_pos _

theorem anchor_one_le (H j : ℕ) : 1 ≤ anchor H j := Real.one_le_exp (by positivity)

theorem growth_one_le (H : ℕ) : 1 ≤ growth H := Real.one_le_exp (by positivity)

theorem growth_error (H : ℕ) (hH : 2 ≤ H) : growth H-1 ≤ 2/(H : ℝ) := by
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hi : 0 ≤ 1/(H : ℝ) := by positivity
  have hi1 : 1/(H : ℝ) ≤ 1 := (div_le_iff₀ (by linarith : (0 : ℝ) < H)).mpr (by linarith)
  have hh := Real.abs_exp_sub_one_le (x := 1/(H : ℝ)) (by rwa [abs_of_nonneg hi])
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hi)),abs_of_nonneg hi] at hh
  exact hh.trans_eq (by ring)

theorem growth_le_two (H : ℕ) (hH : 2 ≤ H) : growth H ≤ 2 := by
  have hh := growth_error H hH
  have hHR : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hi : 2/(H : ℝ) ≤ 1 := (div_le_iff₀ (by linarith : (0 : ℝ) < H)).mpr (by linarith)
  linarith

theorem anchor_successor (H j : ℕ) : anchor H (j+1)=anchor H j*growth H := by
  rw [anchor,Nat.cast_add,Nat.cast_one,add_div,Real.exp_add]
  rfl

theorem index_bounds (H p : ℕ) (hH : 0 < H) (hp : 1 ≤ p) :
    anchor H (index H p) ≤ (p : ℝ) ∧ (p : ℝ) < growth H*anchor H (index H p) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hl := Nat.floor_le (mul_nonneg hHR.le hlog)
  have hu := Nat.lt_floor_add_one ((H : ℝ)*Real.log (p : ℝ))
  constructor
  · calc
      anchor H (index H p) ≤ Real.exp (Real.log (p : ℝ)) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ hHR).mpr
        simpa only [index,mul_comm] using hl
      _ = _ := Real.exp_log hpR
  · calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hpR).symm
      _ < Real.exp (((index H p : ℕ) : ℝ)/(H : ℝ)+1/(H : ℝ)) := by
        apply Real.exp_lt_exp.mpr
        rw [← add_div]
        apply (lt_div_iff₀ hHR).mpr
        simpa only [index,mul_comm] using hu
      _ = _ := by rw [Real.exp_add]; exact mul_comm _ _

theorem band_subset (H : ℕ) (P : Finset ℕ) (j : ℕ) : band H P j ⊆ P := filter_subset _ _

theorem band_bounds (H : ℕ) (hH : 0 < H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p)
    (j p : ℕ) (hp : p ∈ band H P j) : anchor H j ≤ (p : ℝ) ∧ (p : ℝ) < growth H*anchor H j := by
  obtain ⟨hp,hj⟩ := mem_filter.mp hp
  simpa only [hj] using index_bounds H p hH (hP p hp)

theorem band_disjoint (H : ℕ) (P : Finset ℕ) (j k : ℕ) (hjk : j ≠ k) :
    Disjoint (band H P j) (band H P k) := by
  apply disjoint_left.mpr
  intro p hpj hpk
  exact hjk ((mem_filter.mp hpj).2.symm.trans (mem_filter.mp hpk).2)

theorem sum_partition (H : ℕ) (P : Finset ℕ) (a : ℕ → ℂ) :
    (∑ p ∈ P, a p)=∑ j ∈ indices H P, ∑ p ∈ band H P j, a p := by
  symm
  exact sum_fiberwise_of_maps_to (fun p hp ↦ mem_image.mpr ⟨p,hp,rfl⟩) a

theorem indices_card_bound (H : ℕ) (P : Finset ℕ) (U : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p ∧ (p : ℝ) ≤ U) :
    (indices H P).card ≤ ⌊(H : ℝ)*Real.log U⌋₊+1 := by
  have hs : indices H P ⊆ range (⌊(H : ℝ)*Real.log U⌋₊+1) := by
    intro j hj
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    apply mem_range.mpr
    have hlog := Real.log_le_log (by exact_mod_cast (show 0 < p by have := (hP p hp).1; omega)) (hP p hp).2
    have hh := Nat.floor_le_floor (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg H))
    change index H p < _
    dsimp only [index]
    omega
  simpa only [card_range] using card_le_card hs
end PaperP1.NarrowPrimeBands
