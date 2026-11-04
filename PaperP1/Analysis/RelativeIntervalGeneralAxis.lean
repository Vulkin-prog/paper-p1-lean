module

public import PaperP1.Analysis.RelativeIntervalAxisBounds

/-! # Primitive axis costs for an arbitrary fixed lower index proportion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeIntervalGeneralAxis

open Finset PaperP1.RelativeIntervalLattice PaperP1.RelativeIntervalShortVectors
open PaperP1.DeterminantRelativeIntervals PaperP1.BinaryLatticeMinimum PaperP1.BinaryEuclideanReduction
open PaperP1.BinaryLatticeCoordinateBounds PaperP1.PrimitiveBinaryColumns

theorem first_axis_scale (M k : ℕ) (hM : 1 ≤ M) (hk : k ≤ 2 * M)
    (A : ℝ) (hA : 0 ≤ A) (hklow : (M : ℝ) ≤ A * k)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E) (z : Fin 2 → ℤ)
    (hz : (z 0).natAbs.Coprime (z 1).natAbs) (h0 : z 0 = 0) :
    let L := sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) z))
    (M : ℝ) * L ≤ 4 * A * E := by
  have hzne := UnimodularBinaryCoordinates.primitive_nonzero z hz
  have hb := scaled_vector_bounds M k hM hk D E hD hE z hzne
  have hzabs : |(z 1 : ℝ)| = 1 := by exact_mod_cast first_axis_abs z hz h0
  have hkbound := hb.2.2.2
  simp only [h0, Int.cast_zero, mul_zero, sub_zero, abs_mul, hzabs,
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k), one_mul] at hkbound
  have hmul := (le_div_iff₀ hb.1).mp hkbound
  have hlo := mul_le_mul_of_nonneg_right hklow hb.1.le
  nlinarith [mul_le_mul_of_nonneg_left hmul hA]

theorem actual_axis_sums (M : ℕ) (hM : 1 ≤ M) (I : Finset ℕ) (hI : I ⊆ intervalIndices M)
    (A : ℝ) (hA : 0 ≤ A) (hklow : ∀ k ∈ I, (M : ℝ) ≤ A * k)
    (D E : ℝ) (hD : 0 < D) (hE : 0 < E)
    (z : ℕ → Fin 2 → ℤ) (hz : ∀ k ∈ I, (z k 0).natAbs.Coprime (z k 1).natAbs) :
    let L := fun k ↦ sideLength 2 (squareNorm (realImage (transform D E M (intervalCenter M D E k)) (z k)))
    (∑ k ∈ I.filter (fun k ↦ z k 0 = 0), L k) ≤ 8 * A * E ∧
      (∑ k ∈ I.filter (fun k ↦ z k 1 = 0), L k) ≤ 8 * D := by
  have hMp : 0 < M := by omega
  constructor
  · convert RelativeIntervalAxisBounds.scaled_interval_sum_bound M hMp (I.filter (fun k ↦ z k 0 = 0))
      (fun k hk ↦ hI (mem_filter.mp hk).1) _ (4 * A * E) (by positivity) ?_ using 1
    · ring
    · intro k hk
      obtain ⟨hkI, hk0⟩ := mem_filter.mp hk
      exact first_axis_scale M k hM (mem_Icc.mp (hI hkI)).2 A hA (hklow k hkI) D E hD hE (z k) (hz k hkI) hk0
  · convert RelativeIntervalAxisBounds.scaled_interval_sum_bound M hMp (I.filter (fun k ↦ z k 1 = 0))
      (fun k hk ↦ hI (mem_filter.mp hk).1) _ (4 * D) (by positivity) ?_ using 1
    · ring
    · intro k hk
      obtain ⟨hkI, hk1⟩ := mem_filter.mp hk
      exact RelativeIntervalAxisBounds.second_axis_scale M k hM (mem_Icc.mp (hI hkI)).2
        D E hD hE (z k) (hz k hkI) hk1

end PaperP1.RelativeIntervalGeneralAxis
