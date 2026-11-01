module

public import PaperP1.Arithmetic.EvenPrimePatterns
public import PaperP1.Arithmetic.SplitOffsetProducts

/-! # Even prime patterns of actual square-product tuples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KernelTuplePatterns

open Finset PaperP1.Arithmetic PaperP1.SmallPrimeBudget PaperP1.SquarefreeKernelProducts
open PaperP1.EvenPrimePatterns PaperP1.DefectivePredicate PaperP1.LargeOddKernel

theorem kernel_squarefree (n : ℕ) : Squarefree (squarefreeKernel n) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp r hr hpr
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (prime_of_mem_oddPrimeSupport hp) (prime_of_mem_oddPrimeSupport hr)).mpr hpr)
  · intro p hp
    exact (prime_of_mem_oddPrimeSupport hp).squarefree

theorem parityVec_kernel (n : ℕ) (hn : n ≠ 0) :
    parityVec (squarefreeKernel n) = parityVec n := by
  have hpart := canonical_part_ne_zero n hn
  have hk := (squarefreeKernel_pos n).ne'
  have hmul := parityVec_mul hk (pow_ne_zero 2 hpart)
  rw [squarefreeKernel_mul_squarePart hn, parityVec_pow_two, add_zero] at hmul
  exact hmul.symm

theorem kernel_product_square_iff {ι : Type*} (I : Finset ι) (X : ι → ℕ)
    (hX : ∀ i ∈ I, X i ≠ 0) :
    IsSquare (∏ i ∈ I, squarefreeKernel (X i)) ↔ IsSquare (∏ i ∈ I, X i) := by
  have hk : ∀ i ∈ I, squarefreeKernel (X i) ≠ 0 := fun i _ ↦ (squarefreeKernel_pos (X i)).ne'
  rw [← parityVec_eq_zero_iff_isSquare (prod_ne_zero_iff.mpr hk),
    ← parityVec_eq_zero_iff_isSquare (prod_ne_zero_iff.mpr hX),
    parityVec_prod I _ hk, parityVec_prod I X hX]
  have hsum : (∑ i ∈ I, parityVec (squarefreeKernel (X i))) = ∑ i ∈ I, parityVec (X i) :=
    sum_congr rfl (fun i hi ↦ parityVec_kernel (X i) (hX i hi))
  rw [hsum]

theorem actual_even_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → ℕ) (hX : ∀ i, X i ≠ 0) (hsq : IsSquare (∏ i, X i)) :
    let q := fun i ↦ squarefreeKernel (X i)
    (∀ S : Finset ι, 0 < part q S ∧ Squarefree (part q S)) ∧
    (∀ S T : Finset ι, S ≠ T → Nat.Coprime (part q S) (part q T)) ∧
    (∀ i, (∏ S ∈ patterns.filter (fun S ↦ i ∈ S), part q S) = q i) ∧
    ∀ D : Finset ι → ℕ,
      (∀ S ∈ patterns, Squarefree (D S)) →
      (∀ S ∈ patterns, ∀ T ∈ patterns, S ≠ T → Nat.Coprime (D S) (D T)) →
      (∀ i, (∏ S ∈ patterns.filter (fun S ↦ i ∈ S), D S) = q i) →
      ∀ S ∈ patterns, D S = part q S := by
  dsimp only
  let q := fun i ↦ squarefreeKernel (X i)
  have hq : ∀ i, Squarefree (q i) := fun i ↦ kernel_squarefree (X i)
  have hqsq : IsSquare (∏ i, q i) := (kernel_product_square_iff univ X (fun i _ ↦ hX i)).mpr hsq
  exact ⟨fun S ↦ ⟨part_pos q S, part_squarefree q S⟩,
    fun S T hST ↦ part_coprime q S T hST,
    fun i ↦ even_reconstruction q hq hqsq i,
    fun D hD hcop hrec S hS ↦ unique_parts q hq D hD hcop hrec S hS⟩

theorem split_kernel_product_square_iff {ι : Type*} (I : Finset ι)
    (A : Finset ℤ) (n : ι → ℕ) (hX : ∀ i ∈ I, 0 < PaperP1.SplitOffsetProducts.product A (n i)) :
    IsSquare (∏ i ∈ I, PaperP1.SplitOffsetProducts.kernel A (n i)) ↔
      IsSquare (∏ i ∈ I, PaperP1.SplitOffsetProducts.product A (n i)) :=
  kernel_product_square_iff I _ (fun i hi ↦ (hX i hi).ne')

end PaperP1.KernelTuplePatterns
