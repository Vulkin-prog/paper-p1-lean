module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # The literal fractional-linear value map is a bijection away from its pole -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearFractionalValueBijection

variable {F : Type*} [Field F]

theorem denominator_ne_zero {b x : F} (hx : x ≠ -b) : x + b ≠ 0 := by
  intro hz
  apply hx
  linear_combination hz

theorem value_ne_one (a b : F) (hab : a ≠ b) (x : F) (hx : x ≠ -b) :
    (x + a) / (x + b) ≠ 1 := by
  intro h
  have he := (div_eq_iff (denominator_ne_zero hx)).mp h
  apply hab
  linear_combination he

theorem inverse_ne_negative (a b : F) (hab : a ≠ b) (t : F) (ht : t ≠ 1) :
    (a - t * b) / (t - 1) ≠ -b := by
  intro h
  have he := (div_eq_iff (sub_ne_zero.mpr ht)).mp h
  apply hab
  linear_combination he

theorem left_inverse (a b : F) (hab : a ≠ b) (x : F) (hx : x ≠ -b) :
    (a - ((x + a) / (x + b)) * b) / (((x + a) / (x + b)) - 1) = x := by
  have hd := denominator_ne_zero hx
  have ht := sub_ne_zero.mpr (value_ne_one a b hab x hx)
  apply (div_eq_iff ht).mpr
  field_simp [hd]
  ring

theorem right_inverse (a b : F) (hab : a ≠ b) (t : F) (ht : t ≠ 1) :
    (((a - t * b) / (t - 1)) + a) / (((a - t * b) / (t - 1)) + b) = t := by
  have hd := sub_ne_zero.mpr ht
  have hx := denominator_ne_zero (inverse_ne_negative a b hab t ht)
  apply (div_eq_iff hx).mpr
  field_simp [hd]
  ring
def equivalence (a b : F) (hab : a ≠ b) : {x : F // x ≠ -b} ≃ {t : F // t ≠ 1} where
  toFun x := ⟨(x.val + a) / (x.val + b), value_ne_one a b hab x.val x.property⟩
  invFun t := ⟨(a - t.val * b) / (t.val - 1), inverse_ne_negative a b hab t.val t.property⟩
  left_inv x := Subtype.ext (left_inverse a b hab x.val x.property)
  right_inv t := Subtype.ext (right_inverse a b hab t.val t.property)

end PaperP1.LinearFractionalValueBijection
