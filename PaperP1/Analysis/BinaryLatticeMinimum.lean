module

public import PaperP1.Analysis.BinaryEuclideanReduction
public import PaperP1.Arithmetic.PrimitiveBinaryBasis
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Int.Interval

/-! # An actual shortest nonzero vector in every invertible real image of Z squared -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BinaryLatticeMinimum

open Finset PaperP1.BinaryEuclideanReduction PaperP1.UnimodularBinaryCoordinates

def realImage (T : Matrix (Fin 2) (Fin 2) ℝ) (z : Fin 2 → ℤ) : Fin 2 → ℝ :=
  T.mulVec (fun i ↦ (z i : ℝ))

def inverseSize (S : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := max (squareNorm (S 0)) (squareNorm (S 1))

theorem realImage_nonzero (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z : Fin 2 → ℤ) (hz : z ≠ 0) : realImage T z ≠ 0 := by
  intro h
  have hr := reconstruct T S hST (fun i ↦ (z i : ℝ))
  change S.mulVec (realImage T z) = (fun i ↦ (z i : ℝ)) at hr
  rw [h] at hr
  apply hz
  funext i
  have hi : (z i : ℝ) = 0 := by simpa using (congrFun hr i).symm
  exact_mod_cast hi

theorem image_energy_positive (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z : Fin 2 → ℤ) (hz : z ≠ 0) : 0 < squareNorm (realImage T z) :=
  squareNorm_positive _ (realImage_nonzero T S hST z hz)

theorem inverseSize_nonnegative (S : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ inverseSize S :=
  (squareNorm_nonnegative (S 0)).trans (le_max_left _ _)

theorem row_le_inverseSize (S : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2) :
    squareNorm (S i) ≤ inverseSize S := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem coordinate_square_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (z : Fin 2 → ℤ) (i : Fin 2) :
    (z i : ℝ) ^ 2 ≤ inverseSize S * squareNorm (realImage T z) := by
  have hr := congrFun (reconstruct T S hST (fun j ↦ (z j : ℝ))) i
  change (S.mulVec (realImage T z)) i = (z i : ℝ) at hr
  have hd : scalarProduct (S i) (realImage T z) = (z i : ℝ) := by
    simpa only [scalarProduct, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hr
  have hg := gram_identity (S i) (realImage T z)
  rw [hd] at hg
  have hrow := mul_le_mul_of_nonneg_right (row_le_inverseSize S i)
    (squareNorm_nonnegative (realImage T z))
  nlinarith [sq_nonneg (area (S i) (realImage T z))]

theorem sublevel_coordinate_bound (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1)
    (C : ℝ) (z : Fin 2 → ℤ) (hz : squareNorm (realImage T z) ≤ C) (i : Fin 2) :
    |z i| ≤ ⌈inverseSize S * C + 1⌉ := by
  have hs := (coordinate_square_bound T S hST z i).trans
    (mul_le_mul_of_nonneg_left hz (inverseSize_nonnegative S))
  have hscalar : |(z i : ℝ)| ≤ (z i : ℝ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|(z i : ℝ)| - 1), sq_abs (z i : ℝ)]
  have hbound : |(z i : ℝ)| ≤ inverseSize S * C + 1 := by linarith
  have hceil : |(z i : ℝ)| ≤ (⌈inverseSize S * C + 1⌉ : ℤ) := hbound.trans (Int.le_ceil _)
  exact_mod_cast hceil

theorem bounded_sublevels (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) (C : ℝ) :
    ∃ R : ℤ, ∀ z : Fin 2 → ℤ, squareNorm (realImage T z) ≤ C → ∀ i, |z i| ≤ R :=
  ⟨⌈inverseSize S * C + 1⌉, sublevel_coordinate_bound T S hST C⟩

def integerBox (R : ℤ) : Finset (Fin 2 → ℤ) := Fintype.piFinset (fun _ ↦ Finset.Icc (-R) R)

theorem mem_integerBox (R : ℤ) (z : Fin 2 → ℤ) : z ∈ integerBox R ↔ ∀ i, |z i| ≤ R := by
  simp only [integerBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

theorem exists_shortest (T S : Matrix (Fin 2) (Fin 2) ℝ) (hST : S * T = 1) :
    ∃ z : Fin 2 → ℤ, z ≠ 0 ∧
      ∀ w : Fin 2 → ℤ, w ≠ 0 → squareNorm (realImage T z) ≤ squareNorm (realImage T w) := by
  classical
  let u : Fin 2 → ℤ := ![1, 0]
  have hu : u ≠ 0 := by intro h; have h0 := congrFun h 0; norm_num [u] at h0
  obtain ⟨R, hR⟩ := bounded_sublevels T S hST (squareNorm (realImage T u))
  let V := (integerBox R).filter (fun z ↦ z ≠ 0)
  have huV : u ∈ V := mem_filter.mpr ⟨(mem_integerBox R u).mpr (hR u le_rfl), hu⟩
  obtain ⟨z, hzV, hmin⟩ := Finset.exists_min_image V (fun z ↦ squareNorm (realImage T z)) ⟨u, huV⟩
  refine ⟨z, (mem_filter.mp hzV).2, ?_⟩
  intro w hw
  by_cases hwu : squareNorm (realImage T w) ≤ squareNorm (realImage T u)
  · exact hmin w (mem_filter.mpr ⟨(mem_integerBox R w).mpr (hR w hwu), hw⟩)
  · exact (hmin u huV).trans (le_of_lt (lt_of_not_ge hwu))

end PaperP1.BinaryLatticeMinimum
