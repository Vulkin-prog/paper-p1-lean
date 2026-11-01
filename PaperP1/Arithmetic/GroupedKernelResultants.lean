module

public import PaperP1.Arithmetic.SplitOffsetResultantDecomposition

/-! # Resultant control for arbitrary disjoint groupings of the linear factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GroupedKernelResultants

open Finset PaperP1.SplitOffsetProducts PaperP1.SplitOffsetResultantDecomposition
open PaperP1.SquarefreeKernelProducts PaperP1.LinearKernelFibres
open PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate

def grouped (P : Finset (Finset ℤ)) (n : ℕ) : ℕ := ∏ B ∈ P, kernel B n

theorem grouped_pos (P : Finset (Finset ℤ)) (n : ℕ) : 0 < grouped P n :=
  prod_pos (fun B _ ↦ kernel_pos B n)

theorem product_union (P : Finset (Finset ℤ)) (n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id) :
    (∏ B ∈ P, product B n) = product (P.biUnion id) n := by
  unfold product
  rw [prod_biUnion hdis]
  simp only [id_eq]

theorem kernel_grouped (P : Finset (Finset ℤ)) (n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0) :
    squarefreeKernel (grouped P n) = kernel (P.biUnion id) n := by
  have hnonzero : ∀ B ∈ P, product B n ≠ 0 := by
    intro B hB
    apply prod_ne_zero_iff.mpr
    intro a ha
    exact Int.natAbs_ne_zero.mpr (hvalues a (mem_biUnion.mpr ⟨B, hB, ha⟩))
  change squarefreeKernel (∏ B ∈ P, squarefreeKernel (product B n)) = _
  rw [kernel_product_kernels P (fun B ↦ product B n) hnonzero, product_union P n hdis]
  rfl

theorem grouped_divides_linear_product (P : Finset (Finset ℤ)) (n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0) :
    grouped P n ∣ ∏ a ∈ P.biUnion id, linearKernel n a := by
  have hlocal : ∀ B ∈ P, kernel B n ∣ ∏ a ∈ B, linearKernel n a := by
    intro B hB
    obtain ⟨R, _, hR⟩ := linear_product_decomposition B n
      (fun a ha ↦ hvalues a (mem_biUnion.mpr ⟨B, hB, ha⟩))
    exact ⟨R ^ 2, hR⟩
  have hp := prod_dvd_prod_of_dvd (fun B ↦ kernel B n) (fun B ↦ ∏ a ∈ B, linearKernel n a) hlocal
  have heq : (∏ a ∈ P.biUnion id, linearKernel n a) = ∏ B ∈ P, ∏ a ∈ B, linearKernel n a := by
    simpa only [id_eq] using (prod_biUnion (f := fun a ↦ linearKernel n a) hdis)
  rw [heq]
  exact hp

theorem grouped_overlap_decomposition (P : Finset (Finset ℤ)) (n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0) :
    ∃ R : ℕ, R ∣ resultant (P.biUnion id) ∧
      grouped P n = kernel (P.biUnion id) n * R ^ 2 := by
  let A := P.biUnion id
  have hMpos := grouped_pos P n
  have hqpos := kernel_pos A n
  have hrepr := squarefreeKernel_mul_squarePart hMpos.ne'
  rw [kernel_grouped P n hdis hvalues] at hrepr
  change kernel A n * canonicalSquarePart (grouped P n) ^ 2 = grouped P n at hrepr
  have hdiv : grouped P n ∣ kernel A n * resultant A ^ 2 :=
    (grouped_divides_linear_product P n hdis hvalues).trans
      (linear_product_divides_kernel_resultant_square A n hvalues)
  obtain ⟨k, hk⟩ := hdiv
  have hcancel : kernel A n * resultant A ^ 2 =
      kernel A n * (canonicalSquarePart (grouped P n) ^ 2 * k) := by
    calc
      _ = grouped P n * k := hk
      _ = (kernel A n * canonicalSquarePart (grouped P n) ^ 2) * k :=
        congrArg (fun z : ℕ ↦ z * k) hrepr.symm
      _ = _ := by ring
  have heq := Nat.eq_of_mul_eq_mul_left hqpos hcancel
  have hpow : canonicalSquarePart (grouped P n) ^ 2 ∣ resultant A ^ 2 := ⟨k, heq⟩
  exact ⟨canonicalSquarePart (grouped P n), (Nat.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hpow,
    hrepr.symm⟩

theorem grouped_quotient_divides_resultant_square (P : Finset (Finset ℤ)) (n : ℕ)
    (hdis : Set.PairwiseDisjoint (P : Set (Finset ℤ)) id)
    (hvalues : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0) :
    grouped P n / kernel (P.biUnion id) n ∣ resultant (P.biUnion id) ^ 2 := by
  obtain ⟨R, hRD, hR⟩ := grouped_overlap_decomposition P n hdis hvalues
  have hqdiv : kernel (P.biUnion id) n ∣ grouped P n := ⟨R ^ 2, hR⟩
  have heq : kernel (P.biUnion id) n * (grouped P n / kernel (P.biUnion id) n) =
      kernel (P.biUnion id) n * R ^ 2 := by
    rw [mul_comm (kernel (P.biUnion id) n), Nat.div_mul_cancel hqdiv, hR]
  have hquot := Nat.eq_of_mul_eq_mul_left (kernel_pos (P.biUnion id) n) heq
  rw [hquot]
  exact pow_dvd_pow_of_dvd hRD 2

end PaperP1.GroupedKernelResultants
