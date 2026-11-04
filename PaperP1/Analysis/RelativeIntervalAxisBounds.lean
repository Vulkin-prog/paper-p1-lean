module

public import PaperP1.Analysis.RelativeIntervalShortVectors
public import PaperP1.Arithmetic.PrimitiveBinaryColumns

/-! # The primitive axis vectors give the actual D plus E interval costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalAxisBounds

open Finset PaperP1.RelativeIntervalLattice PaperP1.RelativeIntervalShortVectors
open PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BinaryLatticeCoordinateBounds PaperP1.PrimitiveBinaryColumns

theorem first_axis_scale (M k : ℕ) (hM : 1 ≤ M) (hk : k ≤ 2 * M) (hklow : (M : ℝ) / 4 ≤ k)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E) (z : Fin 2 → ℤ)
    (hz : (z 0).natAbs.Coprime (z 1).natAbs) (h0 : z 0 = 0) :
    let L := sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) z))
    (M : ℝ) * L ≤ 16 * E := by
  have hzne := UnimodularBinaryCoordinates.primitive_nonzero z hz
  have hb := scaled_vector_bounds M k hM hk D E hD hE z hzne
  have hzabs : |(z 1 : ℝ)| = 1 := by exact_mod_cast first_axis_abs z hz h0
  have hkbound := hb.2.2.2
  simp only [h0, Int.cast_zero, mul_zero, sub_zero, abs_mul, hzabs,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k), one_mul] at hkbound
  have hmul := (le_div_iff₀ hb.1).mp hkbound
  have hlo := mul_le_mul_of_nonneg_right hklow hb.1.le
  nlinarith

theorem second_axis_scale (M k : ℕ) (hM : 1 ≤ M) (hk : k ≤ 2 * M)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E) (z : Fin 2 → ℤ)
    (hz : (z 0).natAbs.Coprime (z 1).natAbs) (h1 : z 1 = 0) :
    let L := sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) z))
    (M : ℝ) * L ≤ 4 * D := by
  have hzne := UnimodularBinaryCoordinates.primitive_nonzero z hz
  have hb := scaled_vector_bounds M k hM hk D E hD hE z hzne
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hzabs : |(z 0 : ℝ)| = 1 := by exact_mod_cast second_axis_abs z hz h1
  have hkbound := hb.2.2.2
  simp only [h1, Int.cast_zero, zero_mul, zero_sub, abs_neg, abs_mul,
    abs_of_pos (div_pos (mul_pos hMR hE) hD), hzabs, mul_one] at hkbound
  have hmul := (le_div_iff₀ hb.1).mp hkbound
  have hscaled := mul_le_mul_of_nonneg_right hmul hD.le
  field_simp [hD.ne'] at hscaled
  nlinarith only [hscaled]

theorem scaled_interval_sum_bound (M : ℕ) (hM : 0 < M) (I : Finset ℕ)
    (hI : I ⊆ intervalIndices M) (L : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hscale : ∀ k ∈ I, (M : ℝ) * L k ≤ C) : ∑ k ∈ I, L k ≤ 2 * C := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hcard : (I.card : ℝ) ≤ 2 * M := by
    exact_mod_cast (show I.card ≤ 2 * M from (card_le_card hI).trans_eq (intervalIndices_card M))
  apply (mul_le_mul_iff_right₀ hMR).mp
  calc
    _ = ∑ k ∈ I, (M : ℝ) * L k := Finset.mul_sum ..
    _ ≤ ∑ _k ∈ I, C := sum_le_sum hscale
    _ = (I.card : ℝ) * C := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (2 * M) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = _ := by ring

theorem actual_axis_sums (M : ℕ) (hM : 1 ≤ M) (I : Finset ℕ) (hI : I ⊆ intervalIndices M)
    (hklow : ∀ k ∈ I, (M : ℝ) / 4 ≤ k) (D E : ℝ) (hD : 0 < D) (hE : 0 < E)
    (z : ℕ → Fin 2 → ℤ) (hz : ∀ k ∈ I, (z k 0).natAbs.Coprime (z k 1).natAbs) :
    let L := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
    (∑ k ∈ I.filter (fun k ↦ z k 0 = 0), L k) ≤ 32 * E ∧
      (∑ k ∈ I.filter (fun k ↦ z k 1 = 0), L k) ≤ 8 * D := by
  have hMp : 0 < M := by omega
  constructor
  · convert scaled_interval_sum_bound M hMp (I.filter (fun k ↦ z k 0 = 0))
      (fun k hk ↦ hI (mem_filter.mp hk).1) _ (16 * E) (by positivity) ?_ using 1
    · ring
    · intro k hk
      obtain ⟨hkI, hk0⟩ := mem_filter.mp hk
      exact first_axis_scale M k hM (mem_Icc.mp (hI hkI)).2 (hklow k hkI) D E hD hE (z k) (hz k hkI) hk0
  · convert scaled_interval_sum_bound M hMp (I.filter (fun k ↦ z k 1 = 0))
      (fun k hk ↦ hI (mem_filter.mp hk).1) _ (4 * D) (by positivity) ?_ using 1
    · ring
    · intro k hk
      obtain ⟨hkI, hk1⟩ := mem_filter.mp hk
      exact second_axis_scale M k hM (mem_Icc.mp (hI hkI)).2 D E hD hE (z k) (hz k hkI) hk1

end PaperP1.RelativeIntervalAxisBounds
