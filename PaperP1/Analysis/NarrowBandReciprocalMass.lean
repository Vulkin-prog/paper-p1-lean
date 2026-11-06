module

public import PaperP1.Analysis.NarrowRamareRectangle

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowBandReciprocalMass
open Finset PaperP1
open scoped Classical

theorem band_interval_subset (H : ℕ) (hH : 0 < H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (j : ℕ) :
    NarrowPrimeBands.band H P j ⊆ Ico ⌈NarrowPrimeBands.anchor H j⌉₊
      ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ := by
  intro p hp
  have hh := NarrowPrimeBands.band_bounds H hH P hP j p hp
  exact mem_Ico.mpr ⟨Nat.ceil_le.mpr hh.1,Nat.lt_ceil.mpr hh.2⟩

theorem card_bound (H : ℕ) (hH : 0 < H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (j : ℕ) :
    ((NarrowPrimeBands.band H P j).card : ℝ) ≤
      (NarrowPrimeBands.growth H-1)*NarrowPrimeBands.anchor H j+1 := by
  have hu := NarrowPrimeBands.anchor_pos H j
  have hc := NarrowPrimeBands.growth_one_le H
  have hlow : ⌈NarrowPrimeBands.anchor H j⌉₊ ≤ ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ :=
    Nat.ceil_le_ceil (by nlinarith only [hu,hc])
  have hcard := card_le_card (band_interval_subset H hH P hP j)
  rw [Nat.card_Ico] at hcard
  have hcardR : ((NarrowPrimeBands.band H P j).card : ℝ) ≤
      (⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊ : ℝ)-(⌈NarrowPrimeBands.anchor H j⌉₊ : ℝ) := by
    have hh : ((NarrowPrimeBands.band H P j).card : ℝ) ≤
        ((⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊-⌈NarrowPrimeBands.anchor H j⌉₊ : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa only [Nat.cast_sub hlow] using hh
  have hupp := Nat.ceil_lt_add_one (show 0 ≤ NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j by positivity)
  have hlo := Nat.le_ceil (NarrowPrimeBands.anchor H j)
  nlinarith only [hcardR,hupp,hlo]

theorem mass_bound (H : ℕ) (hH : 0 < H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (j : ℕ) :
    (∑ p ∈ NarrowPrimeBands.band H P j, 1/(p : ℝ)) ≤
      NarrowPrimeBands.growth H-1+1/NarrowPrimeBands.anchor H j := by
  have hu := NarrowPrimeBands.anchor_pos H j
  calc
    _ ≤ ∑ _p ∈ NarrowPrimeBands.band H P j, 1/NarrowPrimeBands.anchor H j :=
      sum_le_sum (fun p hp ↦ one_div_le_one_div_of_le hu (NarrowPrimeBands.band_bounds H hH P hP j p hp).1)
    _ = ((NarrowPrimeBands.band H P j).card : ℝ)/NarrowPrimeBands.anchor H j := by
      rw [sum_const,nsmul_eq_mul]
      ring
    _ ≤ ((NarrowPrimeBands.growth H-1)*NarrowPrimeBands.anchor H j+1)/NarrowPrimeBands.anchor H j :=
      div_le_div_of_nonneg_right (card_bound H hH P hP j) hu.le
    _ = _ := by field_simp

theorem mass_bound_precision (H : ℕ) (hH : 2 ≤ H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (j : ℕ) :
    (∑ p ∈ NarrowPrimeBands.band H P j, 1/(p : ℝ)) ≤ 2/(H : ℝ)+1/NarrowPrimeBands.anchor H j := by
  have hh := mass_bound H (by omega) P hP j
  have he := NarrowPrimeBands.growth_error H hH
  linarith only [hh,he]

theorem mass_le_one (H : ℕ) (hH : 4 ≤ H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) (j : ℕ)
    (hu : 2 ≤ NarrowPrimeBands.anchor H j) : (∑ p ∈ NarrowPrimeBands.band H P j, 1/(p : ℝ)) ≤ 1 := by
  have hHR : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have h1 : 2/(H : ℝ) ≤ 1/2 := (div_le_iff₀ (by linarith : (0 : ℝ) < H)).mpr (by linarith)
  have h2 : 1/NarrowPrimeBands.anchor H j ≤ 1/2 :=
    (div_le_iff₀ (NarrowPrimeBands.anchor_pos H j)).mpr (by linarith)
  have hh := mass_bound_precision H (by omega) P hP j
  linarith only [hh,h1,h2]

theorem anchor_lower (H : ℕ) (hH : 2 ≤ H) (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p)
    (Y : ℝ) (hY : ∀ p ∈ P, Y ≤ (p : ℝ)) (j : ℕ) (hj : j ∈ NarrowPrimeBands.indices H P) :
    Y/2 ≤ NarrowPrimeBands.anchor H j := by
  obtain ⟨p,hp,hj⟩ := mem_image.mp hj
  have hh := (NarrowPrimeBands.index_bounds H p (by omega) (hP p hp)).2
  have hg := NarrowPrimeBands.growth_le_two H hH
  rw [hj] at hh
  have hm := mul_le_mul_of_nonneg_right hg (NarrowPrimeBands.anchor_pos H j).le
  nlinarith only [hh,hm,hY p hp]
end PaperP1.NarrowBandReciprocalMass
