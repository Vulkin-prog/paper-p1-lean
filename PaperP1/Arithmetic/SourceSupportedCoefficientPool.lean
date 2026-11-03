module

public import PaperP1.Combinatorics.BoundedSubsets
public import PaperP1.Arithmetic.RelativeSquarefreeParts
public import Mathlib.Basic.Real.Basic

/-! # Actual square-equation coefficients from bounded source supports -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSupportedCoefficientPool

open Finset PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.RelativeSquarefreeParts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positions (R : ℕ) : Finset (Finset ι) := BoundedSubsets.sets univ R

def fibre (v : ι → ℕ) (H : ℕ) (A : Finset ι) : Finset ℕ :=
  ((primorial H).divisors ×ˢ (A.prod v).divisors).image fun ab ↦ ab.1 * ab.2

def pool (v : ι → ℕ) (H R : ℕ) : Finset ℕ := (positions R).biUnion (fibre v H)

theorem mem_positions (R : ℕ) (A : Finset ι) : A ∈ positions R ↔ A.card ≤ R := by
  simp only [positions, BoundedSubsets.mem_sets, subset_univ, true_and]

theorem kernel_mem (v : ι → ℕ) (H R n : ℕ) (A : Finset ι) (hA : A.card ≤ R)
    (hm : 0 < A.prod v) (hdiv : largeOddKernel H n ∣ A.prod v) :
    squarefreeKernel n ∈ pool v H R := by
  apply mem_biUnion.mpr
  refine ⟨A, (mem_positions R A).mpr hA, mem_image.mpr ?_⟩
  refine ⟨(smallOddPart H n, largeOddKernel H n), mem_product.mpr ⟨?_, ?_⟩, small_mul_large H n⟩
  · exact Nat.mem_divisors.mpr ⟨smallOddPart_dvd_primorial H n, (primorial_pos H).ne'⟩
  · exact Nat.mem_divisors.mpr ⟨hdiv, hm.ne'⟩

theorem pool_pos (v : ι → ℕ) (H R : ℕ) {D : ℕ} (hD : D ∈ pool v H R) : 0 < D := by
  obtain ⟨A, _hA, hD⟩ := mem_biUnion.mp hD
  obtain ⟨ab, hab, rfl⟩ := mem_image.mp hD
  obtain ⟨ha, hb⟩ := mem_product.mp hab
  exact Nat.mul_pos (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)

omit [Fintype ι] [DecidableEq ι] in
theorem fibre_card (v : ι → ℕ) (H : ℕ) (A : Finset ι) :
    (fibre v H A).card ≤ (primorial H).divisors.card * (A.prod v).divisors.card :=
  card_image_le.trans_eq (card_product _ _)

theorem card_pool_real (v : ι → ℕ) (H R : ℕ) (D : ℝ)
    (hdiv : ∀ A ∈ positions (ι := ι) R, ((A.prod v).divisors.card : ℝ) ≤ D) :
    ((pool v H R).card : ℝ) ≤ ((positions (ι := ι) R).card : ℝ) *
      ((primorial H).divisors.card : ℝ) * D := by
  have hfinite : (pool v H R).card ≤ ∑ A ∈ positions R, (fibre v H A).card := card_biUnion_le
  calc
    _ ≤ ∑ A ∈ positions R, ((fibre v H A).card : ℝ) := by exact_mod_cast hfinite
    _ ≤ ∑ _A ∈ positions (ι := ι) R, ((primorial H).divisors.card : ℝ) * D := by
      apply sum_le_sum
      intro A hA
      have hcast : ((fibre v H A).card : ℝ) ≤ ((primorial H).divisors.card : ℝ) *
          ((A.prod v).divisors.card : ℝ) := by exact_mod_cast fibre_card v H A
      exact hcast.trans (mul_le_mul_of_nonneg_left (hdiv A hA) (Nat.cast_nonneg _))
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

theorem square_coefficient (v : ι → ℕ) (H R n : ℕ) (hn : 0 < n) (A : Finset ι) (hA : A.card ≤ R)
    (hm : 0 < A.prod v) (hdiv : largeOddKernel H n ∣ A.prod v) :
    ∃ D ∈ pool v H R, IsSquare ((D : ℤ) * n) := by
  refine ⟨squarefreeKernel n, kernel_mem v H R n A hA hm hdiv, ?_⟩
  obtain ⟨r, hr⟩ := kernel_mul_isSquare hn.ne'
  exact ⟨(r : ℤ), by exact_mod_cast hr⟩

end PaperP1.SourceSupportedCoefficientPool
