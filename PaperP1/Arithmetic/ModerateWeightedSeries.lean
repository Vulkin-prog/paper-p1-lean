module

public import PaperP1.Arithmetic.ModerateCertificateCount
public import PaperP1.Analysis.ExponentialPowerSum

/-! # The exact factorial/exponential majorant for all moderate-certificate orders -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ModerateWeightedSeries

open Finset PaperP1.ModerateCertificateCount PaperP1.PrimeProductBudget

def weightedTerm (B N : ℕ) (Y T a : ℝ) (r : ℕ) : ℝ :=
  a ^ r / (r.factorial : ℝ) * ((sourceTuples r B N Y T).card : ℝ)

def weightedTotal (B N : ℕ) (Y T a : ℝ) : ℝ := ∑' r : ℕ, weightedTerm B N Y T a r

def coefficient (B N : ℕ) (Y T : ℝ) : ℝ :=
  18 * (B : ℝ) ^ (assignmentExponent N Y + 4) / T ^ 2

theorem weightedTerm_nonneg (B N : ℕ) (Y T a : ℝ) (ha : 0 ≤ a) (r : ℕ) :
    0 ≤ weightedTerm B N Y T a r := by unfold weightedTerm; positivity

theorem weightedTerm_zero (B N : ℕ) (Y T a : ℝ) : weightedTerm B N Y T a 0 = 0 := by
  simp only [weightedTerm, sourceTuples_zero, card_empty, Nat.cast_zero, mul_zero]

theorem weightedTerm_eq_zero_of_lt (B N : ℕ) (Y T a : ℝ) (r : ℕ) (hNr : N < r) :
    weightedTerm B N Y T a r = 0 := by
  simp only [weightedTerm, sourceTuples_empty_of_lt r B N Y T hNr, card_empty, Nat.cast_zero, mul_zero]

theorem summable_weightedTerm (B N : ℕ) (Y T a : ℝ) : Summable (weightedTerm B N Y T a) := by
  have h : HasSum (weightedTerm B N Y T a) (∑ r ∈ range (N + 1), weightedTerm B N Y T a r) := by
    apply hasSum_sum_of_ne_finset_zero
    intro r hr
    apply weightedTerm_eq_zero_of_lt B N Y T a r
    simp only [mem_range] at hr
    omega
  exact h.summable

theorem weightedTotal_eq_positiveOrders (B N : ℕ) (Y T a : ℝ) :
    weightedTotal B N Y T a = ∑' r : ℕ, weightedTerm B N Y T a (r + 1) := by
  have h := (summable_weightedTerm B N Y T a).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, weightedTerm_zero, zero_add, weightedTotal] using h.symm

theorem finite_weight_identity (B N a T : ℝ) (m r : ℕ) (hr : 1 ≤ r) :
    a ^ r / (r.factorial : ℝ) *
      (36 * (r : ℝ) * B ^ 4 * 2 ^ (r - 1) * N ^ r / T ^ 2 * ((r : ℝ) * B) ^ m) =
        (18 * B ^ (m + 4) / T ^ 2) * PaperP1.ExponentialPowerSum.term (m + 1) (2 * a * N) r := by
  have htwo : (2 : ℝ) ^ (r - 1) = (2 : ℝ) ^ r / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).mpr
    rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [htwo]
  unfold PaperP1.ExponentialPowerSum.term
  simp only [pow_add, pow_one, mul_pow]
  ring

theorem weightedTerm_le (B N : ℕ) (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T a : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) (ha : 0 ≤ a) (r : ℕ) :
    weightedTerm B N Y T a r ≤ coefficient B N Y T *
      PaperP1.ExponentialPowerSum.term (assignmentExponent N Y + 1) (2 * a * N) r := by
  by_cases hr : r = 0
  · subst r
    rw [weightedTerm_zero]
    simp only [PaperP1.ExponentialPowerSum.term, Nat.cast_zero, zero_pow (by omega : assignmentExponent N Y + 1 ≠ 0),
      zero_mul, zero_div, mul_zero, le_refl]
  have hrpos : 1 ≤ r := by omega
  have hfinite := main_7_2_finite r B N hrpos hN hB hBN Y T hY hT
  have h := mul_le_mul_of_nonneg_left hfinite (by positivity : (0 : ℝ) ≤ a ^ r / (r.factorial : ℝ))
  calc
    _ ≤ a ^ r / (r.factorial : ℝ) *
        (36 * (r : ℝ) * (B : ℝ) ^ 4 * 2 ^ (r - 1) * (N : ℝ) ^ r / T ^ 2 *
          (↑(r * B) : ℝ) ^ assignmentExponent N Y) := h
    _ = _ := by
      rw [Nat.cast_mul]
      exact finite_weight_identity B N a T (assignmentExponent N Y) r hrpos

theorem weightedTotal_le (B N : ℕ) (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y T a : ℝ) (hY : (B : ℝ) ≤ Y) (hT : 1 ≤ T) (ha : 0 ≤ a) :
    weightedTotal B N Y T a ≤ coefficient B N Y T *
      ((assignmentExponent N Y + 1).factorial : ℝ) * Real.exp (Real.exp 1 * (2 * a * N)) := by
  have hz : 0 ≤ 2 * a * (N : ℝ) := by positivity
  have hmajor := (PaperP1.ExponentialPowerSum.summable_term (assignmentExponent N Y + 1) (2 * a * N) hz).mul_left
    (coefficient B N Y T)
  have hC : 0 ≤ coefficient B N Y T := by unfold coefficient; positivity
  calc
    _ ≤ ∑' r : ℕ, coefficient B N Y T *
        PaperP1.ExponentialPowerSum.term (assignmentExponent N Y + 1) (2 * a * N) r :=
      (summable_weightedTerm B N Y T a).tsum_le_tsum (weightedTerm_le B N hN hB hBN Y T a hY hT ha) hmajor
    _ = coefficient B N Y T * PaperP1.ExponentialPowerSum.total (assignmentExponent N Y + 1) (2 * a * N) := by
      rw [tsum_mul_left]
      rfl
    _ ≤ coefficient B N Y T *
        (((assignmentExponent N Y + 1).factorial : ℝ) * Real.exp (Real.exp 1 * (2 * a * N))) :=
      mul_le_mul_of_nonneg_left (PaperP1.ExponentialPowerSum.total_le _ _ hz) hC
    _ = _ := by ring

end PaperP1.ModerateWeightedSeries
