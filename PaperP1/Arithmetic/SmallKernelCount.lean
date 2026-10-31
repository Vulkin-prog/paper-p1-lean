module

public import PaperP1.Arithmetic.SmallPrimeBudget
public import PaperP1.Analysis.RankinComparison

/-! # Actual integers with a small truncated odd-prime kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelCount

open Finset PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.SmallPrimeBudget
open PaperP1.DefectivePredicate
open PaperP1.LargeOddKernel PaperP1.RankinComparison PaperP1.PartialPowerSum

def smallKernelValues (Y T X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ largeOddKernel Y n ≤ T

def fibreValues (k : ℕ) (S : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.sqrt (X / (k * S.prod id)))).image
    (fun a ↦ k * S.prod id * a ^ 2)

def eulerProduct (Y : ℕ) (σ : ℝ) : ℝ :=
  ∏ p ∈ smallPrimesUpTo Y, (1 + (p : ℝ) ^ (-σ))

theorem mem_smallKernelValues {Y T X n : ℕ} :
    n ∈ smallKernelValues Y T X ↔ 1 ≤ n ∧ n ≤ X ∧ largeOddKernel Y n ≤ T := by
  simp only [smallKernelValues, mem_filter, mem_Icc, and_assoc]

theorem smallKernelValues_subset_cover (Y T X : ℕ) :
    smallKernelValues Y T X ⊆ (Finset.Icc 1 T).biUnion
      (fun k ↦ (smallPrimesUpTo Y).powerset.biUnion fun S ↦ fibreValues k S X) := by
  intro n hn
  obtain ⟨hn, hnX, hkT⟩ := mem_smallKernelValues.mp hn
  let k := largeOddKernel Y n
  let S := smallOddSupport Y n
  let a := canonicalSquarePart n
  have hk : 0 < k := largeOddKernel_pos Y n
  have hS : 0 < S.prod id := smallOddPart_pos Y n
  have heq : n = k * S.prod id * a ^ 2 := by
    rw [← squarefreeKernel_mul_squarePart (by omega : n ≠ 0),
      ← small_mul_large Y n]
    dsimp [k, S, a, smallOddPart]
    ring
  have ha : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    rw [ha0, pow_two, mul_zero, mul_zero] at heq
    omega
  have haX : a ^ 2 ≤ X / (k * S.prod id) := by
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos hk hS)).mpr
    simpa only [mul_comm (a ^ 2)] using heq ▸ hnX
  refine mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨hk, hkT⟩, ?_⟩
  refine mem_biUnion.mpr ⟨S, mem_powerset.mpr (smallOddSupport_subset Y n), ?_⟩
  exact mem_image.mpr ⟨a, mem_Icc.mpr ⟨ha, (Nat.le_sqrt').mpr haX⟩, heq.symm⟩

theorem card_fibreValues_le (k : ℕ) (S : Finset ℕ) (X : ℕ) :
    (fibreValues k S X).card ≤ Nat.sqrt (X / (k * S.prod id)) := by
  exact card_image_le.trans_eq (by simp [Nat.card_Icc])

theorem card_smallKernelValues_le_sqrt_sum (Y T X : ℕ) :
    (smallKernelValues Y T X).card ≤
      ∑ k ∈ Finset.Icc 1 T, ∑ S ∈ (smallPrimesUpTo Y).powerset,
        Nat.sqrt (X / (k * S.prod id)) := by
  calc
    _ ≤ ((Finset.Icc 1 T).biUnion
        (fun k ↦ (smallPrimesUpTo Y).powerset.biUnion fun S ↦ fibreValues k S X)).card :=
      card_le_card (smallKernelValues_subset_cover Y T X)
    _ ≤ ∑ k ∈ Finset.Icc 1 T,
        ((smallPrimesUpTo Y).powerset.biUnion fun S ↦ fibreValues k S X).card := card_biUnion_le
    _ ≤ ∑ k ∈ Finset.Icc 1 T,
        ∑ S ∈ (smallPrimesUpTo Y).powerset, (fibreValues k S X).card :=
      sum_le_sum fun _ _ ↦ card_biUnion_le
    _ ≤ _ := sum_le_sum fun k _ ↦ sum_le_sum fun S _ ↦ card_fibreValues_le k S X

theorem card_smallKernelValues_le_euler (Y T X : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ((smallKernelValues Y T X).card : ℝ) ≤
      (X : ℝ) ^ σ * powerSum σ T * eulerProduct Y σ := by
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 T) (S : Finset ℕ)
      (hS : S ∈ (smallPrimesUpTo Y).powerset) :
      (Nat.sqrt (X / (k * S.prod id)) : ℝ) ≤
        (X : ℝ) ^ σ * (k : ℝ) ^ (-σ) * ∏ p ∈ S, (p : ℝ) ^ (-σ) := by
    have hprod : 1 ≤ S.prod id := by
      apply Nat.one_le_iff_ne_zero.mpr
      apply prod_ne_zero_iff.mpr
      intro p hp
      exact (mem_smallPrimesUpTo.mp (mem_powerset.mp hS hp)).1.ne_zero
    have hks : 1 ≤ k * S.prod id := by
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := (mem_Icc.mp hk).1; omega)
        (by omega))
    have h := cast_sqrt_div_le_rankin (X := X) hks hσ
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg (S.prod id)),
      cast_prod_rpow] at h
    simpa only [mul_assoc] using h
  calc
    _ ≤ ((∑ k ∈ Finset.Icc 1 T, ∑ S ∈ (smallPrimesUpTo Y).powerset,
        Nat.sqrt (X / (k * S.prod id)) : ℕ) : ℝ) := by
      exact_mod_cast card_smallKernelValues_le_sqrt_sum Y T X
    _ = ∑ k ∈ Finset.Icc 1 T, ∑ S ∈ (smallPrimesUpTo Y).powerset,
        (Nat.sqrt (X / (k * S.prod id)) : ℝ) := by norm_cast
    _ ≤ ∑ k ∈ Finset.Icc 1 T, ∑ S ∈ (smallPrimesUpTo Y).powerset,
        (X : ℝ) ^ σ * (k : ℝ) ^ (-σ) * ∏ p ∈ S, (p : ℝ) ^ (-σ) :=
      sum_le_sum fun k hk ↦ sum_le_sum fun S hS ↦ hterm k hk S hS
    _ = _ := by
      unfold powerSum eulerProduct
      rw [Finset.prod_one_add]
      simp_rw [← mul_sum]
      rw [← sum_mul, ← mul_sum]

theorem eulerProduct_nonneg (Y : ℕ) (σ : ℝ) : 0 ≤ eulerProduct Y σ := by
  apply prod_nonneg
  intro p _
  positivity

theorem eulerProduct_le_exp (Y : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    eulerProduct Y σ ≤ Real.exp ((Y : ℝ) ^ (1 - σ) / (1 - σ)) := by
  have hsub : smallPrimesUpTo Y ⊆ Finset.Icc 1 Y := by
    intro p hp
    obtain ⟨hp, hpY⟩ := mem_smallPrimesUpTo.mp hp
    exact mem_Icc.mpr ⟨hp.one_lt.le, hpY⟩
  calc
    _ ≤ Real.exp (∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-σ)) :=
      Real.prod_one_add_le_exp_sum _ (fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ Real.exp (powerSum σ Y) := by
      apply Real.exp_le_exp.mpr
      exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ _ := Real.exp_le_exp.mpr (powerSum_le σ hσ hσ1 Y)

theorem card_smallKernelValues_le_power (Y T X : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) :
    ((smallKernelValues Y T X).card : ℝ) ≤
      (X : ℝ) ^ σ * ((T : ℝ) ^ (1 - σ) / (1 - σ)) *
        Real.exp ((Y : ℝ) ^ (1 - σ) / (1 - σ)) := by
  have hσ0 : 0 ≤ σ := by linarith
  calc
    _ ≤ (X : ℝ) ^ σ * powerSum σ T * eulerProduct Y σ :=
      card_smallKernelValues_le_euler Y T X σ hσ
    _ ≤ (X : ℝ) ^ σ * ((T : ℝ) ^ (1 - σ) / (1 - σ)) * eulerProduct Y σ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (powerSum_le σ hσ0 hσ1 T) (Real.rpow_nonneg (Nat.cast_nonneg X) _))
        (eulerProduct_nonneg Y σ)
    _ ≤ _ := mul_le_mul_of_nonneg_left (eulerProduct_le_exp Y σ hσ0 hσ1) (by positivity)

end PaperP1.SmallKernelCount
