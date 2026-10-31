module

public import PaperP1.Arithmetic.SmallKernelCount

/-! # Article Lemma 7.1 with real cutoffs and its square-root endpoint -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RankinSmallKernel

open Finset PaperP1.Arithmetic PaperP1.LargeOddKernel PaperP1.SmallKernelCount
open PaperP1.DefectivePredicate

def truncatedKernel (Y : ℝ) (n : ℕ) : ℕ :=
  ((oddPrimeSupport n).filter fun p : ℕ ↦ Y < (p : ℝ)).prod id

def values (X Y T : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor X)).filter fun n ↦ (truncatedKernel Y n : ℝ) ≤ T

def exponentConstant (σ : ℝ) : ℝ := 1 / (1 - σ)

def countConstant (σ C₁ : ℝ) : ℝ := C₁ ^ σ / (1 - σ)

theorem truncatedKernel_eq_floor (Y : ℝ) (hY : 0 ≤ Y) (n : ℕ) :
    truncatedKernel Y n = largeOddKernel (Nat.floor Y) n := by
  unfold truncatedKernel largeOddKernel
  congr 1
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨hp, hcut⟩
    refine ⟨hp, ?_⟩
    by_contra h
    have hle : (p : ℝ) ≤ Y := (Nat.le_floor_iff hY).mp (by omega)
    linarith
  · rintro ⟨hp, hcut⟩
    refine ⟨hp, ?_⟩
    by_contra h
    have hle : p ≤ Nat.floor Y := (Nat.le_floor_iff hY).mpr (by linarith)
    omega

theorem mem_values (X Y T : ℝ) (hX : 0 ≤ X) (n : ℕ) :
    n ∈ values X Y T ↔ 1 ≤ n ∧ (n : ℝ) ≤ X ∧ (truncatedKernel Y n : ℝ) ≤ T := by
  simp only [values, mem_filter, mem_Icc, Nat.le_floor_iff hX, and_assoc]

theorem values_eq_natural (X Y T : ℝ) (hY : 0 ≤ Y) (hT : 0 ≤ T) :
    values X Y T = smallKernelValues (Nat.floor Y) (Nat.floor T) (Nat.floor X) := by
  ext n
  simp only [values, mem_filter, mem_Icc, mem_smallKernelValues, and_assoc,
    truncatedKernel_eq_floor Y hY n, Nat.le_floor_iff hT]

theorem rankin_bound (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1)
    (X Y T : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hT : 0 ≤ T) :
    ((values X Y T).card : ℝ) ≤
      X ^ σ * (T ^ (1 - σ) / (1 - σ)) *
        Real.exp (Y ^ (1 - σ) / (1 - σ)) := by
  have hσ0 : 0 ≤ σ := by linarith
  have hδ : 0 < 1 - σ := by linarith
  have hXpow := Real.rpow_le_rpow (Nat.cast_nonneg (Nat.floor X)) (Nat.floor_le hX) hσ0
  have hTpow := Real.rpow_le_rpow (Nat.cast_nonneg (Nat.floor T)) (Nat.floor_le hT) hδ.le
  have hYpow := Real.rpow_le_rpow (Nat.cast_nonneg (Nat.floor Y)) (Nat.floor_le hY) hδ.le
  rw [values_eq_natural X Y T hY hT]
  calc
    _ ≤ (Nat.floor X : ℝ) ^ σ * ((Nat.floor T : ℝ) ^ (1 - σ) / (1 - σ)) *
        Real.exp ((Nat.floor Y : ℝ) ^ (1 - σ) / (1 - σ)) :=
      card_smallKernelValues_le_power _ _ _ σ hσ hσ1
    _ ≤ _ := mul_le_mul
      (mul_le_mul hXpow (div_le_div_of_nonneg_right hTpow hδ.le) (by positivity)
        (Real.rpow_nonneg hX _))
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hYpow hδ.le))
      (Real.exp_nonneg _) (by positivity)

theorem rankin_half (X Y T : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hT : 0 ≤ T) :
    ((values X Y T).card : ℝ) ≤
      2 * Real.sqrt X * Real.sqrt T * Real.exp (2 * Real.sqrt Y) := by
  have h := rankin_bound (1 / 2) (by norm_num) (by norm_num) X Y T hX hY hT
  norm_num at h
  simp only [← Real.sqrt_eq_rpow] at h
  rw [show Real.sqrt Y / (1 / 2) = 2 * Real.sqrt Y by ring] at h
  convert h using 1
  ring

theorem exponentConstant_pos (σ : ℝ) (hσ : σ < 1) : 0 < exponentConstant σ := by
  unfold exponentConstant
  positivity

theorem countConstant_pos (σ C₁ : ℝ) (hσ : σ < 1) (hC₁ : 0 < C₁) :
    0 < countConstant σ C₁ := by
  exact div_pos (Real.rpow_pos_of_pos hC₁ _) (by linarith)

/-- Explicit uniform constants; this stronger form includes σ=1/2. -/
theorem main_7_1_explicit (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1)
    (C₁ : ℝ) (hC₁ : 0 < C₁) (N : ℕ) (Y T : ℝ) (hY : 0 ≤ Y) (hT : 1 ≤ T) :
    ((values (C₁ * N) Y T).card : ℝ) ≤
      countConstant σ C₁ * (N : ℝ) ^ σ * T ^ (1 - σ) *
        Real.exp (exponentConstant σ * Y ^ (1 - σ)) := by
  have h := rankin_bound σ hσ hσ1 (C₁ * N) Y T (by positivity) hY (by linarith)
  simpa only [countConstant, exponentConstant, Real.mul_rpow hC₁.le (Nat.cast_nonneg N),
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, one_mul] using h

/-- Source quantifier order: the exponential constant depends only on σ. -/
theorem main_7_1 (σ : ℝ) (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ Cσ : ℝ, 0 < Cσ ∧ ∀ C₁ : ℝ, 0 < C₁ → ∃ A : ℝ, 0 < A ∧
      ∀ N : ℕ, ∀ Y T : ℝ, 0 ≤ Y → 1 ≤ T →
        ((values (C₁ * N) Y T).card : ℝ) ≤
          A * (N : ℝ) ^ σ * T ^ (1 - σ) * Real.exp (Cσ * Y ^ (1 - σ)) := by
  refine ⟨exponentConstant σ, exponentConstant_pos σ hσ1, ?_⟩
  intro C₁ hC₁
  exact ⟨countConstant σ C₁, countConstant_pos σ C₁ hσ1 hC₁,
    fun N Y T hY hT ↦ main_7_1_explicit σ hσ.le hσ1 C₁ hC₁ N Y T hY hT⟩

end PaperP1.RankinSmallKernel
