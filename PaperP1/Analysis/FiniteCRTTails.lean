module

public import PaperP1.Analysis.IntegerProductTail
public import PaperP1.Arithmetic.PositiveProductPairs

/-! # Finite positive-integer tails for the two CRT counting regimes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteCRTTails

open Finset PaperP1.PowerSeriesTail PaperP1.IntegerProductTail

theorem positive_power_tail (s T : ℝ) (hs : 1 < s) (hT : 1 ≤ T)
    (S : Finset ℕ) (hS : ∀ q ∈ S, 0 < q ∧ T < (q : ℝ)) :
    (∑ q ∈ S, (q : ℝ) ^ (-s)) ≤ constant s * T ^ (1 - s) := by
  have heq : (∑ q ∈ S, (q : ℝ) ^ (-s)) =
      ∑ n ∈ S.image (fun q ↦ q - 1), tailTerm s T n := by
    rw [sum_image]
    · apply sum_congr rfl
      intro q hq
      have hrec : q - 1 + 1 = q := Nat.sub_add_cancel (hS q hq).1
      have hcast : ((q - 1 : ℕ) : ℝ) + 1 = q := by exact_mod_cast hrec
      simp only [tailTerm, weight, hcast, ite_eq_left (hS q hq).2]
    · intro q hq r hr heqr
      have hqpos := (hS q hq).1
      have hrpos := (hS r hr).1
      change q - 1 = r - 1 at heqr
      omega
  rw [heq]
  exact ((summable_tailTerm s T hs).sum_le_tsum _
    (fun n _ ↦ tailTerm_nonneg s T n)).trans (tail_le_power s hs T hT)

theorem positive_product_power_tail (s T : ℝ) (hs : 1 < s) (hT : 1 ≤ T)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2 ∧ T < (z.1 : ℝ) * z.2) :
    (∑ z ∈ S, ((z.1 : ℝ) * z.2) ^ (-s)) ≤
      productConstant s * T ^ (1 - s) * Real.log (2 * T) := by
  have heq : (∑ z ∈ S, ((z.1 : ℝ) * z.2) ^ (-s)) =
      ∑ z ∈ S.image (fun z ↦ (z.1 - 1, z.2 - 1)), pairTerm s T z := by
    rw [sum_image]
    · apply sum_congr rfl
      intro z hz
      have ha : ((z.1 - 1 : ℕ) : ℝ) + 1 = z.1 := by
        exact_mod_cast Nat.sub_add_cancel (hS z hz).1
      have hb : ((z.2 - 1 : ℕ) : ℝ) + 1 = z.2 := by
        exact_mod_cast Nat.sub_add_cancel (hS z hz).2.1
      rw [pairTerm_eq_power, ha, hb, ite_eq_left (hS z hz).2.2]
    · intro z hz w hw heqzw
      have ha := congrArg Prod.fst heqzw
      have hb := congrArg Prod.snd heqzw
      change z.1 - 1 = w.1 - 1 at ha
      change z.2 - 1 = w.2 - 1 at hb
      have hzdata := hS z hz
      have hwdata := hS w hw
      exact Prod.ext (by omega) (by omega)
  rw [heq]
  exact ((summable_pairTerm s T hs).sum_le_tsum _
    (fun z _ ↦ pairTerm_nonneg s T z)).trans (productTail_bound s hs T hT)

theorem shifted_cube (a : ℝ) (ha : 0 ≤ a) : (a + 1) ^ 3 ≤ 4 * (a ^ 3 + 1) := by
  nlinarith [mul_nonneg (sq_nonneg (a - 1)) (by linarith : 0 ≤ a + 1)]

theorem shifted_square (a : ℝ) : (a + 1) ^ 2 ≤ 2 * (a ^ 2 + 1) := by
  nlinarith [sq_nonneg (a - 1)]

theorem finite_cube_sum (N T R : ℝ) (hN : 0 ≤ N) (hT : 1 ≤ T) (hR : 0 ≤ R)
    (S : Finset ℕ) (hS : ∀ q ∈ S, 0 < q ∧ T < (q : ℝ) ∧ (q : ℝ) ≤ R) :
    (∑ q ∈ S, (N / (q : ℝ) + 1) ^ 3) ≤ 8 * N ^ 3 * T ^ (-2 : ℝ) + 4 * R := by
  have htail := positive_power_tail 3 T (by norm_num) hT S
    (fun q hq ↦ ⟨(hS q hq).1, (hS q hq).2.1⟩)
  have hc : constant 3 = 2 := by norm_num [constant]
  rw [hc, show (1 - (3 : ℝ)) = -2 by norm_num] at htail
  have hcard := PositiveProductPairs.positive_values_count S R hR
    (fun q hq ↦ ⟨(hS q hq).1, (hS q hq).2.2⟩)
  have hterms (q : ℕ) : (N / (q : ℝ)) ^ 3 = N ^ 3 * (q : ℝ) ^ (-3 : ℝ) := by
    rw [div_pow, div_eq_mul_inv]
    congr 1
    norm_num
  calc
    _ ≤ ∑ q ∈ S, 4 * (N ^ 3 * (q : ℝ) ^ (-3 : ℝ) + 1) := by
      apply sum_le_sum
      intro q _
      simpa only [hterms] using shifted_cube (N / (q : ℝ)) (div_nonneg hN (Nat.cast_nonneg q))
    _ = 4 * N ^ 3 * (∑ q ∈ S, (q : ℝ) ^ (-3 : ℝ)) + 4 * S.card := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 4 * N ^ 3)]

theorem finite_square_sum (N T : ℝ) (hT : 1 ≤ T) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2 ∧ T < (z.1 : ℝ) * z.2) :
    (∑ z ∈ S, (N / ((z.1 : ℝ) * z.2) + 1) ^ 2) ≤
      2 * productConstant 2 * N ^ 2 * T ^ (-1 : ℝ) * Real.log (2 * T) + 2 * S.card := by
  have htail := positive_product_power_tail 2 T (by norm_num) hT S hS
  rw [show (1 - (2 : ℝ)) = -1 by norm_num] at htail
  have hterms (z : ℕ × ℕ) : (N / ((z.1 : ℝ) * z.2)) ^ 2 =
      N ^ 2 * ((z.1 : ℝ) * z.2) ^ (-2 : ℝ) := by
    rw [div_pow, div_eq_mul_inv]
    congr 1
    norm_num
  calc
    _ ≤ ∑ z ∈ S, 2 * (N ^ 2 * ((z.1 : ℝ) * z.2) ^ (-2 : ℝ) + 1) := by
      apply sum_le_sum
      intro z _
      simpa only [hterms] using shifted_square (N / ((z.1 : ℝ) * z.2))
    _ = 2 * N ^ 2 * (∑ z ∈ S, ((z.1 : ℝ) * z.2) ^ (-2 : ℝ)) + 2 * S.card := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * N ^ 2)]

end PaperP1.FiniteCRTTails
