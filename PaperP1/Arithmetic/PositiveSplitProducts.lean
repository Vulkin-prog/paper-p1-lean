module

public import PaperP1.Arithmetic.SplitOffsetSupports
public import PaperP1.Arithmetic.SquareEquationKernel
public import PaperP1.Diophantine.LinearKernelFibres

/-! # Split-product heights depend on actual positive values, not the offset positions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveSplitProducts

open Finset PaperP1.SplitOffsetProducts PaperP1.LinearKernelFibres PaperP1.SmallPrimeBudget

theorem product_pos (A : Finset ℤ) (n : ℕ) (hpos : ∀ a ∈ A, 0 < (n : ℤ) + a) :
    0 < product A n :=
  Finset.prod_pos (fun a ha ↦ Int.natAbs_pos.mpr (hpos a ha).ne')

theorem product_cast (A : Finset ℤ) (n : ℕ) (hpos : ∀ a ∈ A, 0 < (n : ℤ) + a) :
    (product A n : ℤ) = ∏ a ∈ A, ((n : ℤ) + a) := by
  rw [product, Nat.cast_prod]
  apply prod_congr rfl
  intro a ha
  rw [← Int.abs_eq_natAbs, abs_of_pos (hpos a ha)]

theorem product_bound (K d N n : ℕ) (hN : 1 ≤ N) (A : Finset ℤ) (hcard : A.card ≤ d)
    (hvalues : ∀ a ∈ A, value n a ≤ N ^ K) : product A n ≤ N ^ (K * d) := by
  calc
    _ ≤ ∏ _a ∈ A, N ^ K := Finset.prod_le_prod hvalues
    _ = (N ^ K) ^ A.card := by rw [prod_const]
    _ ≤ (N ^ K) ^ d := Nat.pow_le_pow_right (one_le_pow₀ hN) hcard
    _ = _ := (pow_mul N K d).symm

theorem difference_bound (n M : ℕ) (a b : ℤ) (ha : 0 < (n : ℤ) + a)
    (hb : 0 < (n : ℤ) + b) (haM : value n a ≤ M) (hbM : value n b ≤ M) :
    (a - b).natAbs ≤ M := by
  have haAbs : |(n : ℤ) + a| ≤ M := by rw [Int.abs_eq_natAbs]; exact_mod_cast haM
  have hbAbs : |(n : ℤ) + b| ≤ M := by rw [Int.abs_eq_natAbs]; exact_mod_cast hbM
  have haUpper := (abs_le.mp haAbs).2
  have hbUpper := (abs_le.mp hbAbs).2
  have hh : |a - b| ≤ (M : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  rw [Int.abs_eq_natAbs] at hh
  exact_mod_cast hh

theorem resultant_bound (K d N n : ℕ) (hN : 1 ≤ N) (A : Finset ℤ) (hcard : A.card ≤ d)
    (hpos : ∀ a ∈ A, 0 < (n : ℤ) + a) (hvalues : ∀ a ∈ A, value n a ≤ N ^ K) :
    resultant A ≤ N ^ (K * d ^ 2) := by
  have hlocal : ∀ ab ∈ pairs A, (ab.1 - ab.2).natAbs ≤ N ^ K := by
    intro ab hab
    obtain ⟨ha, hb, _⟩ := (mem_pairs A ab.1 ab.2).mp hab
    exact difference_bound n (N ^ K) ab.1 ab.2 (hpos _ ha) (hpos _ hb) (hvalues _ ha) (hvalues _ hb)
  calc
    _ ≤ ∏ _ab ∈ pairs A, N ^ K := Finset.prod_le_prod hlocal
    _ = (N ^ K) ^ (pairs A).card := by rw [prod_const]
    _ ≤ (N ^ K) ^ (d ^ 2) := Nat.pow_le_pow_right (one_le_pow₀ hN)
      ((card_pairs A).trans (Nat.pow_le_pow_left hcard 2))
    _ = _ := (pow_mul N K (d ^ 2)).symm

theorem kernel_resultant_bound (K d N n : ℕ) (hN : 1 ≤ N) (A : Finset ℤ) (hcard : A.card ≤ d)
    (hpos : ∀ a ∈ A, 0 < (n : ℤ) + a) (hvalues : ∀ a ∈ A, value n a ≤ N ^ K) :
    kernel A n * resultant A ≤ N ^ (K * (d + d ^ 2)) := by
  calc
    _ ≤ N ^ (K * d) * N ^ (K * d ^ 2) := Nat.mul_le_mul
      ((kernel_le A n (product_pos A n hpos)).trans (product_bound K d N n hN A hcard hvalues))
      (resultant_bound K d N n hN A hcard hpos hvalues)
    _ = _ := by rw [← pow_add]; congr 1; ring

theorem integer_square_kernel (A : Finset ℤ) (n : ℕ) (D : ℤ) (hD : D ≠ 0)
    (hpos : ∀ a ∈ A, 0 < (n : ℤ) + a)
    (hsquare : IsSquare (D * ∏ a ∈ A, ((n : ℤ) + a))) :
    kernel A n = squarefreeKernel D.natAbs := by
  rw [← product_cast A n hpos] at hsquare
  obtain ⟨w, hw⟩ := hsquare
  have habs : IsSquare (D.natAbs * product A n) := by
    refine ⟨w.natAbs, ?_⟩
    have hh := congrArg Int.natAbs hw
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh
  exact (SquareEquationKernel.kernels_eq_of_square_mul (Int.natAbs_ne_zero.mpr hD)
    (product_pos A n hpos).ne' habs).symm

end PaperP1.PositiveSplitProducts
