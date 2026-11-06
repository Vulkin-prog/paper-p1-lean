module

public import PaperP1.Algebra.LinearFractionalValueBijection
public import PaperP1.Arithmetic.QuadraticCharacterLinearSum

/-! # Exact quadratic-character sums for two distinct linear factors

The proof uses the actual fractional-linear bijection, excluding exactly its
pole and the missing value1. No curve point estimate is a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticCharacterTwoFactorSum

open Finset
open scoped Classical

theorem sum_away {α M : Type*} [Fintype α] [AddCommMonoid M] (f : α → M) (a : α) :
    (∑ x : {x : α // x ≠ a}, f x.val) + f a = ∑ x : α, f x := by
  have hs : (∑ x : {x : α // x ≠ a}, f x.val) = ∑ x ∈ (univ : Finset α).erase a, f x :=
    (Finset.sum_subtype ((univ : Finset α).erase a) (by simp) f).symm
  rw [hs]
  exact sum_erase_add (s := (univ : Finset α)) f (mem_univ a)

variable {F : Type*} [Field F] [Fintype F]

theorem product_character (a b x : F) (hx : x ≠ -b) :
    quadraticChar F ((x + a) * (x + b)) = quadraticChar F ((x + a) / (x + b)) := by
  have hd := LinearFractionalValueBijection.denominator_ne_zero hx
  have he : ((x + a) / (x + b)) * (x + b) ^ 2 = (x + a) * (x + b) := by
    field_simp
  rw [← he, map_mul, quadraticChar_sq_one' hd, mul_one]

theorem sum_eq_neg_one (hodd : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) :
    (∑ x : F, quadraticChar F ((x + a) * (x + b))) = -1 := by
  let e := LinearFractionalValueBijection.equivalence a b hab
  have he : (∑ x : {x : F // x ≠ -b}, quadraticChar F ((x.val + a) * (x.val + b))) =
      ∑ t : {t : F // t ≠ 1}, quadraticChar F t.val :=
    Fintype.sum_equiv e _ _ (fun x ↦ product_character a b x.val x.property)
  have hs := sum_away (fun x : F ↦ quadraticChar F ((x + a) * (x + b))) (-b)
  have ht := sum_away (fun t : F ↦ quadraticChar F t) 1
  have hz : quadraticChar F (((-b) + a) * ((-b) + b)) = 0 := by
    rw [neg_add_cancel, mul_zero, quadraticChar_zero]
  rw [hz, add_zero] at hs
  rw [map_one, quadraticChar_sum_zero hodd] at ht
  omega

theorem scaled_sum (hodd : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) (c : F) :
    (∑ x : F, quadraticChar F (c * ((x + a) * (x + b)))) = -quadraticChar F c := by
  have he (x : F) : quadraticChar F (c * ((x + a) * (x + b))) =
      quadraticChar F c * quadraticChar F ((x + a) * (x + b)) := map_mul _ _ _
  simp_rw [he]
  rw [← mul_sum, sum_eq_neg_one hodd a b hab, mul_neg, mul_one]

theorem scaled_sum_abs_le_one (hodd : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) (c : F) :
    |((∑ x : F, quadraticChar F (c * ((x + a) * (x + b))) : ℤ) : ℝ)| ≤ 1 := by
  rw [scaled_sum hodd a b hab, Int.cast_neg, abs_neg]
  exact QuadraticCharacterRootCount.quadratic_character_abs_le_one c

theorem two_shift_sum (hodd : ringChar F ≠ 2) (a b : ℤ) (hab : (a : F) ≠ (b : F)) :
    (∑ x : F, quadraticChar F (SplitRadicalFiniteFieldPointCount.linearValue F {a, b} x)) = -1 := by
  have habZ : a ≠ b := by intro h; exact hab (congrArg (Int.cast : ℤ → F) h)
  simpa only [SplitRadicalFiniteFieldPointCount.linearValue, prod_pair habZ] using
    sum_eq_neg_one hodd (a : F) (b : F) hab

end PaperP1.QuadraticCharacterTwoFactorSum
