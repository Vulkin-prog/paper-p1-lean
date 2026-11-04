module

public import PaperP1.Model.UnsignedUnitFourierAggregate
public import PaperP1.Model.DyadicUnitFourierAggregate
public import PaperP1.Arithmetic.IntervalSourceTranslations

/-! # Actual positive and signed rational-unit sums on arbitrary start intervals

Canonical even selections are reindexed by the original source pairs.
Both orientations are retained before the finite endpoint error is summed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntervalUnitFourierAggregate

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount
  PaperP1.ChannelWordHosts PaperP1.UnitShapePatterns PaperP1.ChannelPlacements
  PaperP1.UnsignedUnitFourierAggregate PaperP1.PrivateUnitCovariance

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def forwardUnsigned (lo hi L a b : ℕ) : ℤ :=
  ∑ p : Patterns L a b, ChannelSumIdentity.weight p.1.val *
    (PaperP1.IntervalSourceTranslations.sourcePairs lo hi a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card

def forwardSigned (lo hi L a b : ℕ) : ℤ :=
  ∑ p : Patterns L a b, coefficient p *
    (PaperP1.IntervalSourceTranslations.sourcePairs lo hi a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card

def sourceCount (lo hi : ℕ) {L a b : ℕ} (p : Patterns L a b) : ℚ :=
  (PaperP1.IntervalSourceTranslations.symmetricSources lo hi a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card

def unsignedHosts (lo hi L a b : ℕ) : ℚ := ∑ p : Patterns L a b, patternWeight p * sourceCount lo hi p

def signedHosts (lo hi L a b : ℕ) : ℚ :=
  ∑ p : Patterns L a b, patternWeight p * patternSign p * sourceCount lo hi p

theorem weighted_unit_hosts (lo hi : ℕ) {L a b : ℕ} (p : Patterns L a b) (κ : ℤ) :
    (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, if HasUnit x y p then κ else 0) =
      κ * (PaperP1.IntervalSourceTranslations.sourcePairs lo hi a b L
        (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card := by
  have hfilter : ((Ico lo hi) ×ˢ (Ico lo hi)).filter (fun xy ↦ HasUnit xy.1 xy.2 p) =
      PaperP1.IntervalSourceTranslations.sourcePairs lo hi a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val) := by
    ext xy
    simp only [mem_filter, HasUnit, mem_units, PaperP1.IntervalSourceTranslations.sourcePairs]
  calc
    _ = ∑ xy ∈ (Ico lo hi) ×ˢ (Ico lo hi), if HasUnit xy.1 xy.2 p then κ else 0 :=
      (sum_product _ _ (fun xy : ℕ × ℕ ↦ if HasUnit xy.1 xy.2 p then κ else 0)).symm
    _ = ∑ xy ∈ ((Ico lo hi) ×ˢ (Ico lo hi)).filter (fun xy ↦ HasUnit xy.1 xy.2 p), κ := (sum_filter _ _).symm
    _ = _ := by rw [hfilter, sum_const, nsmul_eq_mul]; ring

theorem unsigned_integer_sum (lo hi L a b : ℕ) :
    (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, PaperP1.UnsignedUnitWordHosts.integerPatternSum a b x y L) =
      forwardUnsigned lo hi L a b := by
  unfold PaperP1.UnsignedUnitWordHosts.integerPatternSum
  calc
    _ = ∑ x ∈ Ico lo hi, ∑ p : Patterns L a b,
        ∑ y ∈ Ico lo hi, if HasUnit x y p then ChannelSumIdentity.weight p.1.val else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ p : Patterns L a b, ∑ x ∈ Ico lo hi,
        ∑ y ∈ Ico lo hi, if HasUnit x y p then ChannelSumIdentity.weight p.1.val else 0 := sum_comm
    _ = _ := by
      unfold forwardUnsigned
      apply sum_congr rfl
      intro p _
      exact weighted_unit_hosts lo hi p (ChannelSumIdentity.weight p.1.val)

theorem signed_integer_sum (lo hi L a b : ℕ) :
    (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, integerPatternSum a b x y L) = forwardSigned lo hi L a b := by
  unfold integerPatternSum
  calc
    _ = ∑ x ∈ Ico lo hi, ∑ p : Patterns L a b,
        ∑ y ∈ Ico lo hi, if HasUnit x y p then coefficient p else 0 := by
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
    _ = ∑ p : Patterns L a b, ∑ x ∈ Ico lo hi,
        ∑ y ∈ Ico lo hi, if HasUnit x y p then coefficient p else 0 := sum_comm
    _ = _ := by
      unfold forwardSigned
      apply sum_congr rfl
      intro p _
      exact weighted_unit_hosts lo hi p (coefficient p)

theorem unsigned_unit_sum {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, unitWeight a b x y L) = (forwardUnsigned lo hi L a b : ℝ) := by
  calc
    _ = ∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi,
        (PaperP1.UnsignedUnitWordHosts.integerPatternSum a b x y L : ℝ) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      exact PaperP1.UnsignedUnitFourierAggregate.pair_pattern_sum ha hb hab
        (hlo.trans (mem_Ico.mp hx).1) (by have := (mem_Ico.mp hy).1; omega)
    _ = ((∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, PaperP1.UnsignedUnitWordHosts.integerPatternSum a b x y L : ℤ) : ℝ) := by
      simp only [Int.cast_sum]
    _ = _ := congrArg (fun z : ℤ ↦ (z : ℝ)) (unsigned_integer_sum lo hi L a b)

theorem signed_unit_sum {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, signedUnitSum a b x y L) = (forwardSigned lo hi L a b : ℝ) := by
  calc
    _ = ∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, (integerPatternSum a b x y L : ℝ) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      exact PaperP1.DyadicUnitFourierAggregate.pair_pattern_sum ha hb hab
        (hlo.trans (mem_Ico.mp hx).1) (by have := (mem_Ico.mp hy).1; omega)
    _ = ((∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, integerPatternSum a b x y L : ℤ) : ℝ) := by
      simp only [Int.cast_sum]
    _ = _ := congrArg (fun z : ℤ ↦ (z : ℝ)) (signed_integer_sum lo hi L a b)

theorem unsigned_twice_forward {lo hi a b L : ℕ} (hlo : 0 < lo) (hab : a < b)
    (hlarge : (a + b) * (L + 1) + a * L < lo) :
    unsignedHosts lo hi L a b = 2 * (forwardUnsigned lo hi L a b : ℚ) := by
  unfold unsignedHosts sourceCount forwardUnsigned patternWeight
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
  apply sum_congr rfl
  intro p _
  rw [PaperP1.IntervalSourceTranslations.symmetric_card hlo hab hlarge, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem signed_twice_forward {lo hi a b L : ℕ} (hlo : 0 < lo) (hab : a < b)
    (hlarge : (a + b) * (L + 1) + a * L < lo) :
    signedHosts lo hi L a b = 2 * (forwardSigned lo hi L a b : ℚ) := by
  unfold signedHosts sourceCount forwardSigned patternWeight patternSign coefficient
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, mul_sum]
  apply sum_congr rfl
  intro p _
  rw [PaperP1.IntervalSourceTranslations.symmetric_card hlo hab hlarge, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem unsigned_symmetric_sum {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) + a * L < lo) :
    2 * (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, unitWeight a b x y L) = (unsignedHosts lo hi L a b : ℝ) := by
  rw [unsigned_unit_sum hlo ha (ha.trans hab) hcop]
  have hh := congrArg (fun q : ℚ ↦ (q : ℝ)) (unsigned_twice_forward (hi := hi) (by omega : 0 < lo) hab hlarge)
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at hh
  exact hh.symm

theorem signed_symmetric_sum {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) + a * L < lo) :
    2 * (∑ x ∈ Ico lo hi, ∑ y ∈ Ico lo hi, signedUnitSum a b x y L) = (signedHosts lo hi L a b : ℝ) := by
  rw [signed_unit_sum hlo ha (ha.trans hab) hcop]
  have hh := congrArg (fun q : ℚ ↦ (q : ℝ)) (signed_twice_forward (hi := hi) (by omega : 0 < lo) hab hlarge)
  norm_num only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at hh
  exact hh.symm

theorem unsigned_error {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlohi : lo ≤ hi) (hlarge : (a + b) * (L + 1) + a * L < lo)
    (hwidth : b * lo + (a + b) * (L + 1) ≤ a * hi) :
    |unsignedHosts lo hi L a b - 2 * ((hi : ℚ) / b - (lo : ℚ) / a) * (ChannelSumIdentity.unsigned L a b : ℤ)| ≤
      (2 * (((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1)) * (ChannelSumIdentity.unsigned L a b : ℤ) := by
  have hh := PaperP1.WeightedTranslationError.weighted_error (univ : Finset (Patterns L a b))
    patternWeight (fun _ ↦ 1) (sourceCount lo hi) (2 * ((hi : ℚ) / b - (lo : ℚ) / a))
    (2 * (((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1))
    (fun p _ ↦ weight_nonneg p.1.val) (fun _ _ ↦ by norm_num)
    (fun p _ ↦ PaperP1.IntervalSourceTranslations.symmetric_card_error hlo ha hab hcop hlohi hlarge hwidth
      (placementIndex L p.2.1.val) (placementIndex L p.2.2.val))
  simp only [mul_one] at hh
  rw [unsigned_weight_total (ha.trans hab) hab.le] at hh
  exact hh

theorem signed_error {lo hi a b L : ℕ} (hlo : 2 ≤ lo) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlohi : lo ≤ hi) (hlarge : (a + b) * (L + 1) + a * L < lo)
    (hwidth : b * lo + (a + b) * (L + 1) ≤ a * hi) :
    |signedHosts lo hi L a b - 2 * ((hi : ℚ) / b - (lo : ℚ) / a) * (ChannelSumIdentity.signed L a b : ℤ)| ≤
      (2 * (((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1)) * (ChannelSumIdentity.unsigned L a b : ℤ) := by
  have hh := PaperP1.WeightedTranslationError.weighted_error (univ : Finset (Patterns L a b))
    patternWeight patternSign (sourceCount lo hi) (2 * ((hi : ℚ) / b - (lo : ℚ) / a))
    (2 * (((L + 1 : ℕ) : ℚ) / a + ((L + 1 : ℕ) : ℚ) / b + 1))
    (fun p _ ↦ weight_nonneg p.1.val) (fun p _ ↦ (pattern_sign_abs p).le)
    (fun p _ ↦ PaperP1.IntervalSourceTranslations.symmetric_card_error hlo ha hab hcop hlohi hlarge hwidth
      (placementIndex L p.2.1.val) (placementIndex L p.2.2.val))
  rw [signed_weight_total (ha.trans hab) hab.le, unsigned_weight_total (ha.trans hab) hab.le] at hh
  exact hh

end PaperP1.IntervalUnitFourierAggregate
