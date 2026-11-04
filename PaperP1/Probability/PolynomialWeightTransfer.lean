module

public import PaperP1.Probability.PositionalCountTests

/-! # Polynomially weighted total variation from a higher moment and a cutoff

This estimate applies to full configuration laws. It requires actual higher
moments of both nonnegative coefficient sequences.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialWeightTransfer

variable {α : Type*}

theorem weighted_error_le (w a b : α → ℝ) (hw : ∀ x, 1 ≤ w x)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (j q : ℕ) (x : α) :
    w x ^ j * |a x - b x| ≤ w x ^ (j + q) * (a x + b x) := by
  have hw0 := (by norm_num : (0 : ℝ) ≤ 1).trans (hw x)
  have hab : |a x - b x| ≤ a x + b x := by
    have hh := abs_sub_le (a x) 0 (b x)
    simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (ha x), abs_of_nonneg (hb x)] using hh
  exact mul_le_mul (pow_le_pow_right₀ (hw x) (Nat.le_add_right j q)) hab
    (abs_nonneg _) (pow_nonneg hw0 _)

theorem summable_weighted_error (w a b : α → ℝ) (hw : ∀ x, 1 ≤ w x)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (j q : ℕ)
    (hsa : Summable (fun x ↦ w x ^ (j + q) * a x))
    (hsb : Summable (fun x ↦ w x ^ (j + q) * b x)) :
    Summable (fun x ↦ w x ^ j * |a x - b x|) := by
  have hs : Summable (fun x ↦ w x ^ (j + q) * (a x + b x)) := by
    simpa only [mul_add] using hsa.add hsb
  exact Summable.of_nonneg_of_le
    (fun x ↦ mul_nonneg (pow_nonneg (zero_le_one.trans (hw x)) _) (abs_nonneg _))
    (weighted_error_le w a b hw ha hb j q) hs

theorem cutoff_bound (w a b : α → ℝ) (hw : ∀ x, 1 ≤ w x)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) (j q : ℕ) (R : ℝ) (hR : 0 < R)
    (hs0 : Summable (fun x ↦ |a x - b x|))
    (hsa : Summable (fun x ↦ w x ^ (j + q) * a x))
    (hsb : Summable (fun x ↦ w x ^ (j + q) * b x)) :
    (∑' x, w x ^ j * |a x - b x|) ≤
      R ^ j * (∑' x, |a x - b x|) +
        (R ^ q)⁻¹ * ((∑' x, w x ^ (j + q) * a x) +
          ∑' x, w x ^ (j + q) * b x) := by
  have htail : Summable (fun x ↦ w x ^ (j + q) * (a x + b x)) := by
    simpa only [mul_add] using hsa.add hsb
  have hdom (x : α) : w x ^ j * |a x - b x| ≤
      R ^ j * |a x - b x| + (R ^ q)⁻¹ * (w x ^ (j + q) * (a x + b x)) := by
    have hw0 : 0 ≤ w x := zero_le_one.trans (hw x)
    have hab : |a x - b x| ≤ a x + b x := by
      have hh := abs_sub_le (a x) 0 (b x)
      simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (ha x), abs_of_nonneg (hb x)] using hh
    by_cases hx : w x ≤ R
    · have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hw0 hx j) (abs_nonneg (a x - b x))
      have ht : 0 ≤ (R ^ q)⁻¹ * (w x ^ (j + q) * (a x + b x)) :=
        mul_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))
          (mul_nonneg (pow_nonneg hw0 _) (add_nonneg (ha x) (hb x)))
      linarith only [hh, ht]
    · have hp := pow_le_pow_left₀ hR.le (le_of_not_ge hx) q
      have hpower : R ^ q * w x ^ j ≤ w x ^ (j + q) := by
        rw [pow_add]
        nlinarith only [mul_le_mul_of_nonneg_right hp (pow_nonneg hw0 j)]
      have hj : w x ^ j ≤ (R ^ q)⁻¹ * w x ^ (j + q) :=
        (le_inv_mul_iff₀ (pow_pos hR q)).mpr hpower
      have hh := mul_le_mul hj hab (abs_nonneg _) (by positivity)
      have hfirst : 0 ≤ R ^ j * |a x - b x| := by positivity
      nlinarith only [hh, hfirst]
  have hs := summable_weighted_error w a b hw ha hb j q hsa hsb
  have hsum := hs.tsum_le_tsum hdom
    ((hs0.mul_left (R ^ j)).add (htail.mul_left ((R ^ q)⁻¹)))
  rw [(hs0.mul_left (R ^ j)).tsum_add (htail.mul_left ((R ^ q)⁻¹)),
    tsum_mul_left, tsum_mul_left] at hsum
  simpa only [mul_add, hsa.tsum_add hsb] using hsum

end PaperP1.PolynomialWeightTransfer
