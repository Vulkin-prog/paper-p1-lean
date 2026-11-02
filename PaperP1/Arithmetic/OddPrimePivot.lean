module

public import PaperP1.Arithmetic.KernelTuplePatterns
public import PaperP1.Arithmetic.SmallKernelCount
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Actual odd-valuation pivots and their squarefree interpretation

The pivot includes the prime two. Here "odd" refers to the valuation,
not to the parity of the prime. The value for a square is one.

The definition and the cutoff equivalence are adapted from
PaperCPrel8/OddPrimePivot.lean, by Vulkin-prog, Apache-2.0,
commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 1139eb6c2e9978bfe7c6cb8a33a7648fa340bced.
The analytic literature interface of that module is not imported.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OddPrimePivot

open Finset PaperP1.DefectivePredicate PaperP1.DefectCounting
open PaperP1.LargeOddKernel PaperP1.SmallPrimeBudget PaperP1.SquarefreeKernelProducts

def largestOddPrime (n : ℕ) : ℕ := max 1 ((oddPrimeSupport n).sup id)

def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

theorem largestOddPrime_pos (n : ℕ) : 0 < largestOddPrime n :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem largestPrimeFactor_pos (n : ℕ) : 0 < largestPrimeFactor n :=
  lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

theorem largestOddPrime_le_iff {Y n : ℕ} (hY : 1 ≤ Y) :
    largestOddPrime n ≤ Y ↔ HDefective Y n := by
  rw [largestOddPrime, max_le_iff]
  constructor
  · rintro ⟨_, hsup⟩
    rw [hDefective_iff_even_factorization]
    intro p hp hpY
    by_contra hodd
    have hmem : p ∈ oddPrimeSupport n := by
      simp only [oddPrimeSupport, Finsupp.mem_support_iff, oddFactorization,
        Finsupp.mapRange_apply]
      exact fun h ↦ hodd (Nat.dvd_of_mod_eq_zero h)
    have hle : p ≤ Y := (Finset.le_sup (f := id) hmem).trans hsup
    omega
  · intro h
    refine ⟨hY, Finset.sup_le ?_⟩
    intro p hp
    exact (mem_smallPrimesUpTo.mp (oddPrimeSupport_subset_smallPrimesUpTo h hp)).2

theorem largestOddPrime_le_largestPrimeFactor (n : ℕ) :
    largestOddPrime n ≤ largestPrimeFactor n := by
  apply max_le (le_max_left _ _)
  apply le_trans (Finset.sup_le fun p hp ↦
    Finset.le_sup (f := id) (Finsupp.support_mapRange hp))
  exact le_max_right _ _

theorem largestOddPrime_of_squarefree (n : ℕ) (hn : Squarefree n) :
    largestOddPrime n = largestPrimeFactor n := by
  simp only [largestOddPrime, largestPrimeFactor, support_of_squarefree n hn]

theorem support_kernel (n : ℕ) (hn : n ≠ 0) :
    oddPrimeSupport (squarefreeKernel n) = oddPrimeSupport n := by
  ext p
  simp only [mem_oddPrimeSupport_iff_parityVec_ne_zero,
    KernelTuplePatterns.parityVec_kernel n hn]

theorem squarefree_interpretation (n : ℕ) (hn : n ≠ 0) :
    largestOddPrime n = largestPrimeFactor (squarefreeKernel n) := by
  rw [← largestOddPrime_of_squarefree _ (KernelTuplePatterns.kernel_squarefree n)]
  simp only [largestOddPrime, support_kernel n hn]

theorem multiply_square (n a : ℕ) (hn : n ≠ 0) (ha : a ≠ 0) :
    largestOddPrime (n * a ^ 2) = largestOddPrime n := by
  simp only [largestOddPrime, support_mul n (a ^ 2) hn (pow_ne_zero _ ha),
    support_square, Finset.symmDiff_def, sdiff_empty, empty_sdiff, union_empty]

theorem prime_dvd_of_gt_one (n : ℕ) (hn : 1 < largestOddPrime n) :
    (largestOddPrime n).Prime ∧ largestOddPrime n ∣ n := by
  have hsup : 1 < (oddPrimeSupport n).sup id := by
    change 1 < max 1 ((oddPrimeSupport n).sup id) at hn
    exact (lt_max_iff.mp hn).resolve_left (lt_irrefl _)
  have hne : (oddPrimeSupport n).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, sup_empty] at hsup
    exact (by norm_num at hsup)
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup (oddPrimeSupport n) hne id
  have heq' : largestOddPrime n = p := by
    dsimp [largestOddPrime]
    rw [heq]
    dsimp only [id_eq] at *
    exact max_eq_right (by omega)
  rw [heq']
  exact ⟨prime_of_mem_oddPrimeSupport hp,
    Nat.dvd_of_mem_primeFactors (Finsupp.support_mapRange hp)⟩

def pivotValues (X Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ largestOddPrime n ≤ Y

theorem pivotValues_subset_defectValues (X Y : ℕ) (hY : 1 ≤ Y) :
    pivotValues X Y ⊆ defectValues (smallPrimesUpTo Y) X := by
  intro n hn
  obtain ⟨hn, hcut⟩ := mem_filter.mp hn
  obtain ⟨hn1, hnX⟩ := mem_Icc.mp hn
  exact mem_defectValues_of_HDefectRepresentation
    (representationOfHDefective ((largestOddPrime_le_iff hY).mp hcut) (by omega)) hnX

theorem pivot_count_elementary (X Y : ℕ) (hY : 1 ≤ Y) :
    (pivotValues X Y).card ≤ (Nat.sqrt X + 1) * 2 ^ (smallPrimesUpTo Y).card :=
  (card_le_card (pivotValues_subset_defectValues X Y hY)).trans
    (card_HDefectValues_le Y X)

end PaperP1.OddPrimePivot
