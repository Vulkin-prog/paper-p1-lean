module

public import PaperP1.Model.PrivateUnitCovariance
public import Mathlib.FieldTheory.Finiteness

/-! # Actual rational-unit Fourier weights are bounded without any private-coordinate premise -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitFourierWeight

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.PrivateUnitCovariance PaperP1.UnitAffineSigns

local instance unitFourierWeightPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem abs_signed_unit_sum (a b x y L : ℕ) :
    |signedUnitSum a b x y L| ≤ (2 ^ ((units a b x y L).card - 1) : ℝ) - 1 := by
  classical
  let V := LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))
  have hcard : (Fintype.card V : ℝ) = (2 ^ ((units a b x y L).card - 1) : ℝ) := by
    rw [Module.card_eq_pow_finrank (K := F₂), EvenSupportRank.kernel_sum_finrank,
      Fintype.card_coe, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  have hones : (∑ w : V, if w ≠ 0 then (1 : ℝ) else 0) = (Fintype.card V : ℝ) - 1 := by
    have hsplit (w : V) : (if w ≠ 0 then (1 : ℝ) else 0) = 1 - (if w = 0 then 1 else 0) := by
      by_cases hw : w = 0 <;> simp [hw]
    simp_rw [hsplit]
    simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
      sum_ite_eq', mem_univ, ite_true]
  unfold signedUnitSum
  calc
    _ ≤ ∑ w : V, |if w ≠ 0 then (binarySign (leftParity w + rightParity w) : ℝ) else 0| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ w : V, if w ≠ 0 then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro w _
      by_cases hw : w = 0
      · simp only [hw, ne_eq, not_true_eq_false, ite_false, abs_zero]
      · simp only [ite_eq_left hw, binarySign]
        split_ifs <;> norm_num
    _ = _ := hones.trans (congrArg (fun r : ℝ ↦ r - 1) hcard)

theorem unit_kernel_rank_bound {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hx : 0 < x) (hy : 0 < y) :
    (((units a b x y L).card - 1 : ℕ) : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / b := by
  have hcnt := intersection_card_bound (L := L) ha hb hab hx hy
  rw [normalized_intersection_card ha hb hx hy] at hcnt
  by_cases hu : (units a b x y L).card = 0
  · simp only [hu, Nat.zero_sub, Nat.cast_zero]
    positivity
  · have hpos : 1 ≤ (units a b x y L).card := by omega
    rw [Nat.cast_sub hpos, Nat.cast_one]
    linarith

theorem signed_unit_sum_zero_of_card_le_one {a b x y L : ℕ} (hu : (units a b x y L).card ≤ 1) :
    signedUnitSum a b x y L = 0 := by
  have h := abs_signed_unit_sum a b x y L
  have hr : (units a b x y L).card - 1 = 0 := by omega
  rw [hr, pow_zero, sub_self] at h
  exact abs_nonpos_iff.mp h

theorem abs_signed_unit_sum_le_rpow {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hx : 0 < x) (hy : 0 < y) :
    |signedUnitSum a b x y L| ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  calc
    _ ≤ (2 ^ ((units a b x y L).card - 1) : ℝ) - 1 := abs_signed_unit_sum a b x y L
    _ ≤ (2 ^ ((units a b x y L).card - 1) : ℝ) := sub_le_self _ zero_le_one
    _ = (2 : ℝ) ^ (((units a b x y L).card - 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (unit_kernel_rank_bound ha hb hab hx hy)

end PaperP1.UnitFourierWeight
