module

public import PaperP1.Arithmetic.QuadraticCharacterRootCount
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact literal point counts for the quadratic curve, including every branch point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticFiniteFieldPoints

open Finset Polynomial QuadraticCharacterRootCount
open scoped Classical

variable {F : Type*} [Field F] [Fintype F]

def points (f : F[X]) : Finset (F × F) := univ.filter (fun w ↦ w.2 ^ 2 = f.eval w.1)
def goodX (f : F[X]) : Finset F := univ.filter (fun x ↦ quadraticChar F (f.eval x) = 1)
def branchX (f : F[X]) : Finset F := univ.filter (fun x ↦ f.eval x = 0)

theorem mem_points (f : F[X]) (w : F × F) : w ∈ points f ↔ w.2 ^ 2 = f.eval w.1 := by
  simp only [points, Finset.mem_filter, Finset.mem_univ, true_and]

theorem character_cardinality (hodd : ringChar F ≠ 2) (f : F[X]) :
    ((points f).card : ℤ) = Fintype.card F + ∑ x : F, quadraticChar F (f.eval x) := by
  let e : {w : F × F // w.2 ^ 2 = f.eval w.1} ≃ Σ x : F, {y : F // y ^ 2 = f.eval x} :=
    { toFun := fun w ↦ ⟨w.val.1, w.val.2, w.property⟩
      invFun := fun w ↦ ⟨(w.1, w.2.val), w.2.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hc : (points f).card = Fintype.card {w : F × F // w.2 ^ 2 = f.eval w.1} := by
    symm
    exact Fintype.card_of_finset' (p := {w : F × F | w.2 ^ 2 = f.eval w.1}) (points f)
      (fun w ↦ by simp only [points, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq])
  rw [hc, Fintype.card_congr e, Fintype.card_sigma, Nat.cast_sum]
  simp_rw [scalar_cardinality hodd]
  rw [sum_add_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]

theorem cardinality_decomposition (hodd : ringChar F ≠ 2) (f : F[X]) :
    (points f).card = 2 * (goodX f).card + (branchX f).card := by
  have hval (a : F) : (1 + quadraticChar F a) =
      (if quadraticChar F a = 1 then (2 : ℤ) else 0) + (if a = 0 then (1 : ℤ) else 0) := by
    by_cases ha : a = 0
    · norm_num [ha, quadraticChar_zero]
    · rcases quadraticChar_dichotomy ha with h | h <;> norm_num [h, ha]
  have ht : ((points f).card : ℤ) = ∑ x : F, (1 + quadraticChar F (f.eval x)) := by
    rw [character_cardinality hodd, sum_add_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  have hg : (∑ x : F, if quadraticChar F (f.eval x) = 1 then (2 : ℤ) else 0) =
      2 * ((goodX f).card : ℤ) := by
    rw [← sum_filter]
    simp only [goodX, sum_const, nsmul_eq_mul]
    ring
  have hb : (∑ x : F, if f.eval x = 0 then (1 : ℤ) else 0) = ((branchX f).card : ℤ) := by
    rw [← sum_filter]
    simp only [branchX, sum_const, nsmul_eq_mul, mul_one]
  simp_rw [hval] at ht
  rw [sum_add_distrib, hg, hb] at ht
  exact_mod_cast ht

theorem branch_card_le (f : F[X]) (hf : f ≠ 0) : (branchX f).card ≤ f.natDegree := by
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  change x ∈ branchX f at hx
  exact (Polynomial.mem_roots hf).mpr (Finset.mem_filter.mp hx).2

theorem good_root (f : F[X]) (x : F) (hx : x ∈ goodX f) :
    ∃ y : F, y ≠ 0 ∧ y ^ 2 = f.eval x := by
  have hchar := (Finset.mem_filter.mp hx).2
  have hne : f.eval x ≠ 0 := by
    intro hz
    rw [hz, quadraticChar_zero] at hchar
    norm_num at hchar
  obtain ⟨y, hy⟩ := (quadraticChar_one_iff_isSquare hne).mp hchar
  have hs : y ^ 2 = f.eval x := by simpa only [pow_two] using hy.symm
  refine ⟨y, ?_, hs⟩
  intro hz
  exact hne (by rw [← hs, hz, zero_pow (by decide : 2 ≠ 0)])

end PaperP1.HyperellipticFiniteFieldPoints
