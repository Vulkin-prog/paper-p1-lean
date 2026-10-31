module

public import PaperP1.Arithmetic.SmallKernelCount
public import PaperP1.Analysis.PowerSeriesTail

/-! # Positive integers whose odd-prime support belongs to a finite set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothSquarefreeCount

open Finset PaperP1.Arithmetic PaperP1.DefectivePredicate
open PaperP1.SmallKernelCount PaperP1.RankinComparison

def naturalValues (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ oddPrimeSupport n ⊆ P

def values (P : Finset ℕ) (X : ℝ) : Finset ℕ := naturalValues P (Nat.floor X)

def eulerProduct (P : Finset ℕ) (σ : ℝ) : ℝ := ∏ p ∈ P, (1 + (p : ℝ) ^ (-σ))

theorem mem_naturalValues {P : Finset ℕ} {X n : ℕ} :
    n ∈ naturalValues P X ↔ 1 ≤ n ∧ n ≤ X ∧ oddPrimeSupport n ⊆ P := by
  simp only [naturalValues, mem_filter, mem_Icc, and_assoc]

theorem mem_values (P : Finset ℕ) (X : ℝ) (hX : 0 ≤ X) (n : ℕ) :
    n ∈ values P X ↔ 1 ≤ n ∧ (n : ℝ) ≤ X ∧ oddPrimeSupport n ⊆ P := by
  simp only [values, mem_naturalValues, Nat.le_floor_iff hX]

theorem naturalValues_subset_cover (P : Finset ℕ) (X : ℕ) :
    naturalValues P X ⊆ P.powerset.biUnion fun S ↦ fibreValues 1 S X := by
  intro n hn
  obtain ⟨hn, hnX, hs⟩ := mem_naturalValues.mp hn
  let S := oddPrimeSupport n
  let a := canonicalSquarePart n
  have heq : n = S.prod id * a ^ 2 := canonical_odd_mul_sq_decomposition (by omega)
  have hprod : 0 < S.prod id := by
    apply prod_pos
    intro p hp
    exact (PaperP1.LargeOddKernel.prime_of_mem_oddPrimeSupport hp).pos
  have ha : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    rw [ha0, pow_two, mul_zero, mul_zero] at heq
    omega
  have haX : a ^ 2 ≤ X / S.prod id := by
    apply (Nat.le_div_iff_mul_le hprod).mpr
    simpa only [mul_comm (a ^ 2)] using heq ▸ hnX
  refine mem_biUnion.mpr ⟨S, mem_powerset.mpr hs, ?_⟩
  unfold fibreValues
  simp only [one_mul]
  exact mem_image.mpr ⟨a, mem_Icc.mpr ⟨ha, (Nat.le_sqrt').mpr haX⟩, heq.symm⟩

theorem card_naturalValues_le_sqrt_sum (P : Finset ℕ) (X : ℕ) :
    (naturalValues P X).card ≤ ∑ S ∈ P.powerset, Nat.sqrt (X / S.prod id) := by
  calc
    _ ≤ (P.powerset.biUnion fun S ↦ fibreValues 1 S X).card := card_le_card (naturalValues_subset_cover P X)
    _ ≤ ∑ S ∈ P.powerset, (fibreValues 1 S X).card := card_biUnion_le
    _ ≤ _ := sum_le_sum fun S _ ↦ by simpa only [one_mul] using card_fibreValues_le 1 S X

theorem card_naturalValues_le_euler (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p)
    (X : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ((naturalValues P X).card : ℝ) ≤ (X : ℝ) ^ σ * eulerProduct P σ := by
  have hterm (S : Finset ℕ) (hS : S ∈ P.powerset) :
      (Nat.sqrt (X / S.prod id) : ℝ) ≤ (X : ℝ) ^ σ * ∏ p ∈ S, (p : ℝ) ^ (-σ) := by
    have hprod : 1 ≤ S.prod id := by
      apply Nat.one_le_iff_ne_zero.mpr
      apply prod_ne_zero_iff.mpr
      intro p hp
      have h := hP p (mem_powerset.mp hS hp)
      exact ne_of_gt (zero_lt_one.trans_le h)
    simpa only [cast_prod_rpow] using cast_sqrt_div_le_rankin (X := X) hprod hσ
  calc
    _ ≤ ((∑ S ∈ P.powerset, Nat.sqrt (X / S.prod id) : ℕ) : ℝ) := by
      exact_mod_cast card_naturalValues_le_sqrt_sum P X
    _ = ∑ S ∈ P.powerset, (Nat.sqrt (X / S.prod id) : ℝ) := by norm_cast
    _ ≤ ∑ S ∈ P.powerset, (X : ℝ) ^ σ * ∏ p ∈ S, (p : ℝ) ^ (-σ) := sum_le_sum hterm
    _ = _ := by rw [← mul_sum, ← prod_one_add]; rfl

theorem eulerProduct_nonneg (P : Finset ℕ) (σ : ℝ) : 0 ≤ eulerProduct P σ := by
  apply prod_nonneg
  intro p _
  positivity

theorem card_values_le_euler (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p)
    (X : ℝ) (hX : 0 ≤ X) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ((values P X).card : ℝ) ≤ X ^ σ * eulerProduct P σ := by
  calc
    _ ≤ (Nat.floor X : ℝ) ^ σ * eulerProduct P σ := card_naturalValues_le_euler P hP _ σ hσ
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hX) (by linarith)) (eulerProduct_nonneg P σ)

theorem one_mem_values (P : Finset ℕ) (X : ℝ) (hX : 1 ≤ X) : 1 ∈ values P X := by
  apply (mem_values P X (by linarith) 1).mpr
  refine ⟨le_rfl, by simpa using hX, ?_⟩
  simp [oddPrimeSupport, oddFactorization]

theorem card_values_pos (P : Finset ℕ) (X : ℝ) (hX : 1 ≤ X) : 0 < (values P X).card :=
  card_pos.mpr ⟨1, one_mem_values P X hX⟩

theorem one_le_zeta_series (s : ℝ) (hs : 1 < s) : 1 ≤ PaperP1.PowerSeriesTail.total s := by
  have h := (PaperP1.PowerSeriesTail.summable_weight s hs).sum_le_tsum ({0} : Finset ℕ)
    (fun n _ ↦ PaperP1.PowerSeriesTail.weight_nonneg s n)
  simpa only [sum_singleton, PaperP1.PowerSeriesTail.weight, Nat.cast_zero, zero_add,
    Real.one_rpow, PaperP1.PowerSeriesTail.total] using h

theorem card_values_le_source_rankin (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (X : ℝ) (hX : 0 ≤ X) (σ : ℝ) (hσ : 1 / 2 < σ) :
    ((values P X).card : ℝ) ≤
      X ^ σ * PaperP1.PowerSeriesTail.total (2 * σ) * eulerProduct P σ := by
  calc
    _ ≤ X ^ σ * eulerProduct P σ := card_values_le_euler P (fun p hp ↦ (hP p hp).pos) X hX σ hσ.le
    _ ≤ _ := by
      have hζ := one_le_zeta_series (2 * σ) (by linarith)
      have h := mul_le_mul_of_nonneg_left hζ (mul_nonneg (Real.rpow_nonneg hX σ) (eulerProduct_nonneg P σ))
      simpa only [mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

end PaperP1.SmoothSquarefreeCount
