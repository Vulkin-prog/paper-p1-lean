module

public import PaperP1.Probability.AtomicTests
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A polynomial test of a summable signed sequence via a fixed higher moment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialTestTruncation

theorem test_bound (a f : ℕ → ℝ) (d r : ℕ) (hdr : d ≤ r) (K R : ℝ)
    (hK : 0 ≤ K) (hR : 1 ≤ R) (ha : Summable a)
    (hm : Summable (fun k : ℕ ↦ |a k| * (1 + (k : ℝ)) ^ r))
    (hf : ∀ k : ℕ, |f k| ≤ K * (1 + (k : ℝ)) ^ d) :
    Summable (fun k : ℕ ↦ a k * f k) ∧
      |∑' k : ℕ, a k * f k| ≤ K * R ^ d * (∑' k : ℕ, |a k|) +
        (K / R ^ (r - d)) * (∑' k : ℕ, |a k| * (1 + (k : ℝ)) ^ r) := by
  have hRpos : 0 < R := by linarith only [hR]
  have hs : Summable (fun k : ℕ ↦ a k * f k) := by
    apply (hm.mul_left K).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    have hp := pow_le_pow_right₀ (by linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k] :
      (1 : ℝ) ≤ 1 + k) hdr
    have h := mul_le_mul_of_nonneg_left ((hf k).trans (mul_le_mul_of_nonneg_left hp hK)) (abs_nonneg (a k))
    nlinarith only [h]
  refine ⟨hs, ?_⟩
  have hpoint (k : ℕ) : |a k * f k| ≤ K * R ^ d * |a k| +
      (K / R ^ (r - d)) * (|a k| * (1 + (k : ℝ)) ^ r) := by
    have hw : 0 ≤ 1 + (k : ℝ) := by positivity
    rw [abs_mul]
    by_cases hsmall : 1 + (k : ℝ) ≤ R
    · have htest := (hf k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw hsmall d) hK)
      have hmain := mul_le_mul_of_nonneg_left htest (abs_nonneg (a k))
      have htail : 0 ≤ (K / R ^ (r - d)) * (|a k| * (1 + (k : ℝ)) ^ r) := by positivity
      nlinarith only [hmain, htail]
    · have hlarge : R ≤ 1 + (k : ℝ) := le_of_not_ge hsmall
      have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hRpos.le hlarge (r - d))
        (pow_nonneg hw d)
      have hpow : (1 + (k : ℝ)) ^ (r - d) * (1 + (k : ℝ)) ^ d = (1 + (k : ℝ)) ^ r := by
        rw [← pow_add, Nat.sub_add_cancel hdr]
      rw [hpow] at hp
      have hdiv : (1 + (k : ℝ)) ^ d ≤ (1 + (k : ℝ)) ^ r / R ^ (r - d) :=
        (le_div_iff₀ (pow_pos hRpos _)).mpr (by simpa only [mul_comm] using hp)
      have htest := (hf k).trans (mul_le_mul_of_nonneg_left hdiv hK)
      have hmain := mul_le_mul_of_nonneg_left htest (abs_nonneg (a k))
      have hfirst : 0 ≤ K * R ^ d * |a k| := by positivity
      have heq : |a k| * (K * ((1 + (k : ℝ)) ^ r / R ^ (r - d))) =
          K / R ^ (r - d) * (|a k| * (1 + (k : ℝ)) ^ r) := by ring
      rw [heq] at hmain
      exact hmain.trans (le_add_of_nonneg_left hfirst)
  have hsum := hs.abs.tsum_le_tsum hpoint
    (((ha.abs.mul_left (K * R ^ d)).add (hm.mul_left (K / R ^ (r - d)))))
  rw [(ha.abs.mul_left (K * R ^ d)).tsum_add (hm.mul_left (K / R ^ (r - d))),
    tsum_mul_left, tsum_mul_left] at hsum
  have habs : |∑' k : ℕ, a k * f k| ≤ ∑' k : ℕ, |a k * f k| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  exact habs.trans hsum

end PaperP1.PolynomialTestTruncation
