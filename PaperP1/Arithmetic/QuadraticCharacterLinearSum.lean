module

public import PaperP1.Arithmetic.SplitRadicalFiniteFieldPointCount

/-! # Exact cancellation for a singleton branch, and exact counts when every nonempty subset has one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticCharacterLinearSum

open Finset SplitRadicalFiniteFieldPointCount
open scoped Classical

theorem shifted_sum_zero {F : Type*} [Field F] [Fintype F] (hodd : ringChar F ≠ 2) (a : F) :
    (∑ x : F, quadraticChar F (x + a)) = 0 := by
  have he : (∑ x : F, quadraticChar F (x + a)) = ∑ x : F, quadraticChar F x :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ ↦ rfl)
  exact he.trans (quadraticChar_sum_zero hodd)

theorem singleton_sum_zero {F : Type*} [Field F] [Fintype F] (hodd : ringChar F ≠ 2) (a : ℤ) :
    (∑ x : F, quadraticChar F (linearValue F {a} x)) = 0 := by
  simpa only [linearValue, prod_singleton] using shifted_sum_zero hodd (a : F)

theorem exact_count_of_singleton_unions {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (hodd : ringChar F ≠ 2) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (hsingle : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      (∃ a : ℤ, s.biUnion I = {a}) ∨ (∃ b : ℤ, s.biUnion J = {b})) :
    (points c I J).card = Fintype.card F ^ 2 := by
  have hc := character_expansion hodd c I J hI hJ
  have hzero : ∀ s ∈ (univ : Finset ι).powerset.erase ∅,
      quadraticChar F (∏ i ∈ s, c i) *
        (∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x)) *
        (∑ y : F, quadraticChar F (linearValue F (s.biUnion J) y)) = 0 := by
    intro s hs
    rcases hsingle s hs with ⟨a, ha⟩ | ⟨b, hb⟩
    · rw [ha, singleton_sum_zero hodd a, mul_zero, zero_mul]
    · rw [hb, singleton_sum_zero hodd b, mul_zero]
  have hsum := sum_erase_add (s := (univ : Finset ι).powerset)
    (fun s ↦ quadraticChar F (∏ i ∈ s, c i) *
      (∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x)) *
      (∑ y : F, quadraticChar F (linearValue F (s.biUnion J) y)))
    (empty_mem_powerset (s := univ))
  rw [sum_eq_zero hzero, zero_add, ← hc] at hsum
  have hempty : quadraticChar F (∏ i ∈ (∅ : Finset ι), c i) *
      (∑ x : F, quadraticChar F (linearValue F ((∅ : Finset ι).biUnion I) x)) *
      (∑ y : F, quadraticChar F (linearValue F ((∅ : Finset ι).biUnion J) y)) =
      (Fintype.card F : ℤ) ^ 2 := by simp [linearValue, pow_two]
  rw [hempty] at hsum
  exact_mod_cast hsum.symm

end PaperP1.QuadraticCharacterLinearSum
