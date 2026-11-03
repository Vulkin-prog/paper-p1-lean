module

public import PaperP1.Model.SelectedUnitFourierEnumeration
public import PaperP1.Arithmetic.UnsignedUnitWordHosts
public import PaperP1.Model.UnitFourierWeight

/-! # Count every nonzero rational-unit relation, including incompatible ones -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnsignedUnitFourierAggregate

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.SelectedUnitWords PaperP1.ChannelGapWords PaperP1.ChannelWordHosts
  PaperP1.SelectedUnitFourierEnumeration PaperP1.UnsignedUnitWordHosts
  PaperP1.SelectedUnitWordBijection

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def unitWeight (a b x y L : ℕ) : ℝ := (2 ^ ((units a b x y L).card - 1) : ℝ) - 1

theorem unitWeight_nonneg (a b x y L : ℕ) : 0 ≤ unitWeight a b x y L := by
  unfold unitWeight
  exact sub_nonneg.mpr (one_le_pow₀ (by norm_num))

theorem unitWeight_zero_of_card_le_one {a b x y L : ℕ}
    (hu : (units a b x y L).card ≤ 1) : unitWeight a b x y L = 0 := by
  have hr : (units a b x y L).card - 1 = 0 := by omega
  simp only [unitWeight, hr, pow_zero, sub_self]

theorem unitWeight_le_rpow {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (hx : 0 < x) (hy : 0 < y) :
    unitWeight a b x y L ≤ (2 : ℝ) ^ (((L + 1 : ℕ) : ℝ) / b) := by
  calc
    _ ≤ (2 ^ ((units a b x y L).card - 1) : ℝ) := sub_le_self _ zero_le_one
    _ = (2 : ℝ) ^ (((units a b x y L).card - 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (PaperP1.UnitFourierWeight.unit_kernel_rank_bound ha hb hab hx hy)

theorem unit_weight_enumeration {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) :
    unitWeight a b x y L = ((∑ s : Shapes a b x y L, ChannelSumIdentity.weight s.1.val : ℤ) : ℝ) := by
  let V := LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))
  have hcard : (Fintype.card V : ℝ) = (2 ^ ((units a b x y L).card - 1) : ℝ) := by
    rw [Module.card_eq_pow_finrank (K := F₂), EvenSupportRank.kernel_sum_finrank,
      Fintype.card_coe, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  have hnonzero : (∑ w : {w : V // w ≠ 0}, (1 : ℝ)) = unitWeight a b x y L := by
    rw [sum_const, nsmul_eq_mul, card_univ, mul_one,
      Fintype.card_subtype_compl (fun w : V ↦ w = 0)]
    simp only [Fintype.card_unique]
    rw [Nat.cast_sub (Fintype.card_pos), Nat.cast_one, hcard]
    rfl
  rw [← hnonzero]
  calc
    _ = ∑ e : Encodings a b x y L, (1 : ℝ) := by
      symm
      apply Fintype.sum_equiv (kernelEquiv ha hb hab hx hy)
      intro e
      rfl
    _ = _ := by
      change (∑ e : (Σ s : Shapes a b x y L, Words s.1.val), (1 : ℝ)) = _
      rw [Fintype.sum_sigma, Int.cast_sum]
      apply sum_congr rfl
      intro s _
      rw [sum_const, nsmul_eq_mul, card_univ, mul_one,
        weight_eq_word_card (by have hd := (mem_Icc.mp s.1.property).1; omega)]
      norm_cast

theorem pair_pattern_sum {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hy : 0 < y) : unitWeight a b x y L = (integerPatternSum a b x y L : ℝ) := by
  rw [unit_weight_enumeration ha hb hab hx hy, shape_sum]

theorem dyadic_unit_sum {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight a b x y L) = (forwardHosts N L a b : ℝ) := by
  calc
    _ = ∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, (integerPatternSum a b x y L : ℝ) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      exact pair_pattern_sum ha hb hab (by have := (mem_Ico.mp hx).1; omega)
        (by have := (mem_Ico.mp hy).1; omega)
    _ = ((∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, integerPatternSum a b x y L : ℤ) : ℝ) := by
      simp only [Int.cast_sum]
    _ = _ := congrArg (fun z : ℤ ↦ (z : ℝ)) (integer_dyadic_sum N L a b)

theorem symmetric_unit_sum {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight a b x y L) =
      (unsignedHosts N L a b : ℝ) := by
  rw [dyadic_unit_sum hN ha (ha.trans hab) hcop]
  have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (unsigned_hosts_twice_forward (by omega : 0 < N) hab hlarge)
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at h
  exact h.symm

theorem finite_unsigned_sum_error {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    |2 * (∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight a b x y L) -
      (N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ)| ≤
        6 * ((L + 1 : ℕ) : ℝ) * (ChannelSumIdentity.unsigned L a b : ℤ) := by
  have hQ := ChannelWordHosts.unsigned_error hN ha hab hinterior hcop hlarge
  have hR := (Rat.cast_le (K := ℝ)).mpr hQ
  norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_intCast, Rat.cast_ofNat] at hR
  rw [← symmetric_unit_sum hN ha hab hcop hlarge] at hR
  exact hR

end PaperP1.UnsignedUnitFourierAggregate
