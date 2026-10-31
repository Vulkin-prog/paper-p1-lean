module

public import PaperP1.Arithmetic.LogarithmicPrimeCount

@[expose] public section

/-! # Uniform finite bounds for products of small-prime supports -/

namespace PaperP1.SmoothSupportBounds

open Finset DefectCounting

theorem supportProduct_pos {H : ℕ} {S : Finset ℕ}
    (hS : S ⊆ smallPrimesUpTo H) :
    0 < S.prod id := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_smallPrimesUpTo.mp (hS hp)).1.pos

theorem supportProduct_le_primorial {H : ℕ} {S : Finset ℕ}
    (hS : S ⊆ smallPrimesUpTo H) :
    S.prod id ≤ primorial H := by
  calc
    S.prod id ≤ (smallPrimesUpTo H).prod id := by
      apply Finset.prod_le_prod_of_subset_of_one_le hS
      intro p hp _
      exact (mem_smallPrimesUpTo.mp hp).1.one_lt.le
    _ = primorial H := by simp [smallPrimesUpTo, primorial]

theorem supportProduct_le_four_pow {H : ℕ} {S : Finset ℕ}
    (hS : S ⊆ smallPrimesUpTo H) :
    S.prod id ≤ 4 ^ H :=
  (supportProduct_le_primorial hS).trans (primorial_le_four_pow H)

/-- Every smooth squarefree coefficient has one polynomial-height bound,
uniformly over all supports and all logarithmic cutoffs. -/
theorem four_pow_cutoff_le_polynomial
    {N H K : ℕ} {D : ℝ} (hN : 1 ≤ N)
    (hH : (H : ℝ) ≤ D * Real.log N)
    (hK : D * Real.log 4 ≤ (K : ℝ)) :
    4 ^ H ≤ N ^ K := by
  have hlogFour : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : ((4 ^ H : ℕ) : ℝ) ≤ ((N ^ K : ℕ) : ℝ) := by
    calc
      ((4 ^ H : ℕ) : ℝ) = Real.exp ((H : ℝ) * Real.log 4) := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ Real.exp ((D * Real.log N) * Real.log 4) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hH hlogFour.le)
      _ = (N : ℝ) ^ (D * Real.log 4) := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring
      _ ≤ (N : ℝ) ^ (K : ℝ) := Real.rpow_le_rpow_of_exponent_le hNone hK
      _ = ((N ^ K : ℕ) : ℝ) := by simp only [Real.rpow_natCast, Nat.cast_pow]
  exact_mod_cast hcast

end PaperP1.SmoothSupportBounds

