module

public import PaperP1.Arithmetic.QuadraticCharacterTwoFactorSum
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Operations

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SplitProductInversion
open Polynomial Finset
open scoped Classical
variable {F : Type*} [Field F]

def linearProduct (S : Finset F) : F[X] := ∏ b ∈ S, (X + C b)
def invertedProduct (S : Finset F) (a : F) : F[X] :=
  ∏ b ∈ S.erase a, (1 + C (b - a) * X)

theorem linear_degree (S : Finset F) : (linearProduct S).natDegree = S.card := by
  unfold linearProduct
  rw [natDegree_prod_of_monic S _ (fun _ _ ↦ monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]

theorem inverted_factor_degree (a b : F) (h : b ≠ a) :
    (1 + C (b-a) * X : F[X]).natDegree = 1 := by
  rw [add_comm, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_C_mul_X _ (sub_ne_zero.mpr h)
  · rw [natDegree_C_mul_X _ (sub_ne_zero.mpr h), natDegree_one]
    decide

theorem inverted_degree (S : Finset F) (a : F) (ha : a ∈ S) :
    (invertedProduct S a).natDegree = S.card - 1 := by
  unfold invertedProduct
  rw [natDegree_prod]
  · calc
      (∑ b ∈ S.erase a, (1 + C (b-a) * X : F[X]).natDegree) = ∑ b ∈ S.erase a, 1 :=
        sum_congr rfl (fun b hb ↦ inverted_factor_degree a b (mem_erase.mp hb).1)
      _ = (S.erase a).card := by simp
      _ = S.card - 1 := card_erase_of_mem ha
  · intro b hb
    have hd := inverted_factor_degree a b (mem_erase.mp hb).1
    intro hz
    rw [hz, natDegree_zero] at hd
    omega

def inversionEquiv (a : F) : {x : F // x ≠ -a} ≃ {t : F // t ≠ 0} where
  toFun x := ⟨(x.val+a)⁻¹, inv_ne_zero (PaperP1.LinearFractionalValueBijection.denominator_ne_zero x.property)⟩
  invFun t := ⟨t.val⁻¹-a, by
    intro h
    have hz : t.val⁻¹ = 0 := by linear_combination h
    exact t.property (inv_eq_zero.mp hz)⟩
  left_inv x := by apply Subtype.ext; simp only [inv_inv, add_sub_cancel_right]
  right_inv t := by apply Subtype.ext; simp only [sub_add_cancel, inv_inv]

theorem factor_inversion (a b x : F) (hx : x ≠ -a) :
    (x+b)*(x+a)⁻¹ = 1+(b-a)*(x+a)⁻¹ := by
  have hd := PaperP1.LinearFractionalValueBijection.denominator_ne_zero hx
  field_simp
  ring

theorem evaluation_inversion (S : Finset F) (a : F) (ha : a ∈ S)
    (x : F) (hx : x ≠ -a) :
    (linearProduct S).eval x * ((x+a)⁻¹)^S.card =
      (invertedProduct S a).eval ((x+a)⁻¹) := by
  have hd := PaperP1.LinearFractionalValueBijection.denominator_ne_zero hx
  have hfac : ∀ b : F, (x+b)*(x+a)⁻¹ = 1+(b-a)*(x+a)⁻¹ := fun b ↦ factor_inversion a b x hx
  simp only [linearProduct, invertedProduct, eval_prod, eval_add, eval_X, eval_C,
    eval_one, eval_mul]
  rw [← prod_const, ← prod_mul_distrib]
  simp_rw [hfac]
  have he := prod_erase_mul (s := S) (fun b ↦ 1+(b-a)*(x+a)⁻¹) ha
  simpa only [sub_self, zero_mul, add_zero, mul_one] using he.symm

theorem inverted_zero (S : Finset F) (a : F) : (invertedProduct S a).eval 0 = 1 := by
  simp only [invertedProduct, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X,
    mul_zero, add_zero, prod_const_one]

theorem linear_root (S : Finset F) (a : F) (ha : a ∈ S) : (linearProduct S).eval (-a) = 0 := by
  simp only [linearProduct, eval_prod]
  exact prod_eq_zero ha (by simp)

variable [Fintype F]

theorem character_inversion (S : Finset F) (a : F) (ha : a ∈ S) (heven : Even S.card)
    (x : F) (hx : x ≠ -a) :
    quadraticChar F ((linearProduct S).eval x) =
      quadraticChar F ((invertedProduct S a).eval ((x+a)⁻¹)) := by
  have ht : (x+a)⁻¹ ≠ 0 := inv_ne_zero (PaperP1.LinearFractionalValueBijection.denominator_ne_zero hx)
  have hp : quadraticChar F (((x+a)⁻¹)^S.card) = 1 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk, pow_add, ← pow_two, quadraticChar_sq_one' (pow_ne_zero _ ht)]
  have he := congrArg (quadraticChar F) (evaluation_inversion S a ha x hx)
  rw [map_mul, hp, mul_one] at he
  exact he

theorem character_sum_inversion (S : Finset F) (a : F) (ha : a ∈ S) (heven : Even S.card) :
    (∑ x : F, quadraticChar F ((linearProduct S).eval x)) =
      (∑ t : F, quadraticChar F ((invertedProduct S a).eval t)) - 1 := by
  have he : (∑ x : {x : F // x ≠ -a}, quadraticChar F ((linearProduct S).eval x.val)) =
      ∑ t : {t : F // t ≠ 0}, quadraticChar F ((invertedProduct S a).eval t.val) :=
    Fintype.sum_equiv (inversionEquiv a) _ _ (fun x ↦ character_inversion S a ha heven x.val x.property)
  have hs := PaperP1.QuadraticCharacterTwoFactorSum.sum_away
    (fun x : F ↦ quadraticChar F ((linearProduct S).eval x)) (-a)
  have ht := PaperP1.QuadraticCharacterTwoFactorSum.sum_away
    (fun t : F ↦ quadraticChar F ((invertedProduct S a).eval t)) 0
  rw [linear_root S a ha, quadraticChar_zero, add_zero] at hs
  rw [inverted_zero, map_one] at ht
  omega


end PaperP1.SplitProductInversion
