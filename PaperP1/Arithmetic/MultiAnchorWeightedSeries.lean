module

public import PaperP1.Arithmetic.MultiAnchorCertificateCount
public import PaperP1.Analysis.ExponentialPowerSum

/-! # The factorial/exponential majorant for all t-anchor moderate orders -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorWeightedSeries

open Finset PaperP1.MultiAnchorCertificateCount PaperP1.MultiAnchorPrimeBudget

def weightedTerm (t B N : ℕ) (Y T a : ℝ) (r : ℕ) : ℝ :=
  a ^ r / (r.factorial : ℝ) * ((sourceTuples t r B N Y T).card : ℝ)

def weightedTotal (t B N : ℕ) (Y T a : ℝ) : ℝ := ∑' r : ℕ, weightedTerm t B N Y T a r

def coefficient (t B N : ℕ) (Y T : ℝ) : ℝ :=
  (6 : ℝ) ^ t / 2 * (B : ℝ) ^ (assignmentExponent t N Y + 2 * t) / T ^ t

theorem weightedTerm_nonneg (t B N : ℕ) (Y T a : ℝ) (ha : 0 ≤ a) (r : ℕ) :
    0 ≤ weightedTerm t B N Y T a r := by unfold weightedTerm; positivity

theorem weightedTerm_zero (t B N : ℕ) (Y T a : ℝ) : weightedTerm t B N Y T a 0 = 0 := by
  simp only [weightedTerm, sourceTuples_zero, card_empty, Nat.cast_zero, mul_zero]

theorem weightedTerm_eq_zero_of_lt (t B N : ℕ) (Y T a : ℝ) (r : ℕ) (hNr : N < r) :
    weightedTerm t B N Y T a r = 0 := by
  simp only [weightedTerm, sourceTuples_empty_of_lt t r B N Y T hNr, card_empty, Nat.cast_zero, mul_zero]

theorem summable_weightedTerm (t B N : ℕ) (Y T a : ℝ) : Summable (weightedTerm t B N Y T a) := by
  have h : HasSum (weightedTerm t B N Y T a) (∑ r ∈ range (N + 1), weightedTerm t B N Y T a r) := by
    apply hasSum_sum_of_ne_finset_zero
    intro r hr
    apply weightedTerm_eq_zero_of_lt t B N Y T a r
    simp only [mem_range] at hr
    omega
  exact h.summable

theorem weightedTotal_eq_positiveOrders (t B N : ℕ) (Y T a : ℝ) :
    weightedTotal t B N Y T a = ∑' r : ℕ, weightedTerm t B N Y T a (r + 1) := by
  have h := (summable_weightedTerm t B N Y T a).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, weightedTerm_zero, zero_add, weightedTotal] using h.symm

theorem finite_weight_identity (t : ℕ) (B N a T : ℝ) (m r : ℕ) (hr : 1 ≤ r) :
    a ^ r / (r.factorial : ℝ) *
      ((6 : ℝ) ^ t * (r : ℝ) * B ^ (2 * t) * 2 ^ (r - 1) * N ^ r / T ^ t * ((r : ℝ) * B) ^ m) =
        ((6 : ℝ) ^ t / 2 * B ^ (m + 2 * t) / T ^ t) * PaperP1.ExponentialPowerSum.term (m + 1) (2 * a * N) r := by
  have htwo : (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [htwo]
  unfold PaperP1.ExponentialPowerSum.term
  simp only [pow_add, pow_one, mul_pow]
  ring

theorem weightedTerm_le (t B N : ℕ) (ht : 1 ≤ t) (hN : 3 ^ t < N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T a : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) (ha : 0 ≤ a) (r : ℕ) :
    weightedTerm t B N Y T a r ≤ coefficient t B N Y T *
      PaperP1.ExponentialPowerSum.term (assignmentExponent t N Y + 1) (2 * a * N) r := by
  by_cases hr : r = 0
  · subst r
    rw [weightedTerm_zero]
    simp only [PaperP1.ExponentialPowerSum.term, Nat.cast_zero, zero_pow (by omega : assignmentExponent t N Y + 1 ≠ 0),
      zero_mul, zero_div, mul_zero, le_refl]
  have hrpos : 1 ≤ r := by omega
  have hfinite := finite_bound t r B N ht hrpos hN hB hBN Y T hY hT
  have h := mul_le_mul_of_nonneg_left hfinite (by positivity : (0 : ℝ) ≤ a ^ r / (r.factorial : ℝ))
  calc
    _ ≤ a ^ r / (r.factorial : ℝ) *
        ((6 : ℝ) ^ t * (r : ℝ) * (B : ℝ) ^ (2 * t) * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ t *
          (↑(r * B) : ℝ) ^ assignmentExponent t N Y) := h
    _ = _ := by
      rw [Nat.cast_mul]
      exact finite_weight_identity t B N a T (assignmentExponent t N Y) r hrpos

theorem weightedTotal_le (t B N : ℕ) (ht : 1 ≤ t) (hN : 3 ^ t < N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T a : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) (ha : 0 ≤ a) :
    weightedTotal t B N Y T a ≤ coefficient t B N Y T *
      ((assignmentExponent t N Y + 1).factorial : ℝ) * Real.exp (Real.exp 1 * (2 * a * N)) := by
  have hz : 0 ≤ 2 * a * (N : ℝ) := by positivity
  have hmajor := (PaperP1.ExponentialPowerSum.summable_term (assignmentExponent t N Y + 1) (2 * a * N) hz).mul_left
    (coefficient t B N Y T)
  have hC : 0 ≤ coefficient t B N Y T := by unfold coefficient; positivity
  calc
    _ ≤ ∑' r : ℕ, coefficient t B N Y T *
        PaperP1.ExponentialPowerSum.term (assignmentExponent t N Y + 1) (2 * a * N) r :=
      (summable_weightedTerm t B N Y T a).tsum_le_tsum (weightedTerm_le t B N ht hN hB hBN Y T a hY hT ha) hmajor
    _ = coefficient t B N Y T * PaperP1.ExponentialPowerSum.total (assignmentExponent t N Y + 1) (2 * a * N) := by
      rw [tsum_mul_left]
      rfl
    _ ≤ coefficient t B N Y T *
        (((assignmentExponent t N Y + 1).factorial : ℝ) * Real.exp (Real.exp 1 * (2 * a * N))) :=
      mul_le_mul_of_nonneg_left (PaperP1.ExponentialPowerSum.total_le _ _ hz) hC
    _ = _ := by ring

end PaperP1.MultiAnchorWeightedSeries
