module

public import PaperP1.Arithmetic.FiniteEulerAverage
public import PaperP1.Analysis.InverseSqrtTail
public import PaperP1.Combinatorics.MarkedGraphGenerator

/-! # Uniform moments of the actual rough-prime Euler product at a square-of-width cutoff -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RoughEulerMoments

open Finset PaperP1.FiniteEulerAverage

def halfWeight (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))

def increment (B p : ℕ) : ℝ := (1 + halfWeight p) ^ B - 1

theorem increment_nonneg (B p : ℕ) : 0 ≤ increment B p := by
  have ht : 0 ≤ halfWeight p := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (show 1 ≤ 1 + halfWeight p by linarith) B
  simpa only [one_pow, increment, sub_nonneg] using h

theorem increment_bound (B p : ℕ) (hp : Nat.Prime p) (hrough : 64 * B ^ 2 < p) :
    increment B p ≤ 8 * (B : ℝ) * halfWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ht : 0 ≤ halfWeight p := Real.rpow_nonneg hpR.le _
  have hroot : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
  have hsquare : (8 * (B : ℝ)) ^ 2 < p := by
    have h : (64 : ℝ) * (B : ℝ) ^ 2 < p := by exact_mod_cast hrough
    nlinarith only [h]
  have hlarge : 8 * (B : ℝ) < Real.sqrt p := (Real.lt_sqrt (by positivity)).mpr hsquare
  let u := (B : ℝ) * halfWeight p
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg B) (Real.rpow_nonneg hpR.le _)
  have husmall : u < 1 / 8 := by
    dsimp [u, halfWeight]
    rw [PaperP1.rpow_neg_one_half_eq_inv_sqrt _ hpR.le, ← div_eq_mul_inv]
    exact (div_lt_iff₀ hroot).mpr (by linarith only [hlarge])
  have hpower : (1 + halfWeight p) ^ B ≤ Real.exp u := by
    calc
      _ ≤ (Real.exp (halfWeight p)) ^ B := pow_le_pow_left₀ (by linarith only [ht])
        (by linarith only [Real.add_one_le_exp (halfWeight p)]) _
      _ = _ := by rw [← Real.exp_nat_mul]
  have hexp := MarkedGraphGenerator.exponential_error_le_rational u hu (by linarith only [husmall])
  have hfrac : 4 * u / (1 - 4 * u) ≤ 8 * u := by
    apply (div_le_iff₀ (by linarith only [husmall] : 0 < 1 - 4 * u)).mpr
    have h := mul_nonneg hu (show 0 ≤ 1 - 8 * u by linarith only [husmall])
    nlinarith only [h]
  calc
    _ ≤ Real.exp u - 1 := sub_le_sub_right hpower 1
    _ ≤ 8 * u := hexp.trans hfrac
    _ = _ := by dsimp [u]; ring

theorem increment_sum (B : ℕ) (hB : 1 ≤ B) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hrough : ∀ p ∈ P, 64 * B ^ 2 < p) :
    (∑ p ∈ P, increment B p / p) ≤ 2 := by
  let Y := 64 * B ^ 2
  have hY : 1 ≤ Y := by dsimp [Y]; nlinarith only [hB]
  have hsub : P ⊆ Ioc Y (P.sup id) := by
    intro p hp
    exact mem_Ioc.mpr ⟨hrough p hp, le_sup (f := id) hp⟩
  have hsum : (∑ p ∈ P, (p : ℝ) ^ (-3 / 2 : ℝ)) ≤ 2 / Real.sqrt Y :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)).trans
      (InverseSqrtTail.tail_bound Y (P.sup id) hY)
  have hroot : Real.sqrt (Y : ℝ) = 8 * B := by
    have heq : (Y : ℝ) = (8 * (B : ℝ)) ^ 2 := by dsimp [Y]; push_cast; ring
    rw [heq, Real.sqrt_sq (by positivity)]
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  calc
    _ ≤ ∑ p ∈ P, 8 * (B : ℝ) * (p : ℝ) ^ (-3 / 2 : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
      calc
        _ ≤ (8 * (B : ℝ) * halfWeight p) / p :=
          div_le_div_of_nonneg_right (increment_bound B p (hP p hp) (hrough p hp)) hpR.le
        _ = _ := by
          rw [halfWeight, div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hpR]
          congr 1
          congr 1
          ring
    _ = 8 * (B : ℝ) * ∑ p ∈ P, (p : ℝ) ^ (-3 / 2 : ℝ) := (mul_sum _ _ _).symm
    _ ≤ 8 * (B : ℝ) * (2 / Real.sqrt Y) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 := by rw [hroot]; field_simp

theorem moment_bound (B : ℕ) (hB : 1 ≤ B) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hrough : ∀ p ∈ P, 64 * B ^ 2 < p) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, (localProduct P halfWeight n) ^ B) ≤ (X : ℝ) * Real.exp 2 := by
  have hpower (n : ℕ) : (localProduct P halfWeight n) ^ B = localProduct P (increment B) n := by
    rw [localProduct, localProduct, ← prod_pow]
    apply prod_congr rfl
    intro p _
    dsimp [increment]
    ring
  simp_rw [hpower]
  calc
    _ ≤ (X : ℝ) * ∏ p ∈ P, (1 + increment B p / p) :=
      average_bound P hP (increment B) (fun p _ ↦ increment_nonneg B p) X
    _ ≤ (X : ℝ) * Real.exp (∑ p ∈ P, increment B p / p) := mul_le_mul_of_nonneg_left
      (Real.prod_one_add_le_exp_sum _ (fun p ↦ div_nonneg (increment_nonneg B p) (Nat.cast_nonneg p))) (Nat.cast_nonneg X)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (increment_sum B hB P hP hrough)) (Nat.cast_nonneg X)

end PaperP1.RoughEulerMoments
