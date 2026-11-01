module

public import PaperP1.Arithmetic.ChannelSelectionCount

/-! # True within-window placements, predecessor signs and the channel sums -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ChannelPlacements

open Finset PaperP1.ChannelSumIdentity

def placements (L D : ℕ) : Finset ℕ := if D ≤ L then range (L + 1 - D) else ∅

def placementSign (j : ℕ) : ℤ := if j = 0 then -1 else 1

def signedPlacements (L D : ℕ) : ℤ := ∑ j ∈ placements L D, placementSign j

theorem placement_card {L D : ℕ} (hD : D ≤ L) : (placements L D).card = L + 1 - D := by
  simp only [placements, ite_eq_left hD, card_range]

theorem placements_empty {L D : ℕ} (hD : L < D) : placements L D = ∅ := by
  exact ite_eq_right (by omega)

theorem signed_placements {L D : ℕ} (hD : D ≤ L) : signedPlacements L D = (L : ℤ) - 1 - D := by
  have hlen : L + 1 - D = (L - D) + 1 := by omega
  rw [signedPlacements, placements, ite_eq_left hD, hlen, sum_range_succ']
  simp only [placementSign, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, ite_true,
    sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hD]
  ring

theorem signed_placements_empty {L D : ℕ} (hD : L < D) : signedPlacements L D = 0 := by
  rw [signedPlacements, placements_empty hD, sum_empty]

theorem exact_contact (L : ℕ) : (placements L L).card = 1 ∧ signedPlacements L L = -1 := by
  constructor
  · rw [placement_card le_rfl]
    omega
  · rw [signed_placements le_rfl]
    ring

def unsignedPairSum (L a b : ℕ) : ℤ :=
  ∑ d ∈ Icc 1 (L / b), weight d * (placements L (a * d)).card * (placements L (b * d)).card

def signedPairSum (L a b : ℕ) : ℤ :=
  ∑ d ∈ Icc 1 (L / b), weight d * signedPlacements L (a * d) * signedPlacements L (b * d)

theorem diameters_fit {L a b d : ℕ} (hb : 0 < b) (hab : a ≤ b) (hd : d ≤ L / b) :
    a * d ≤ L ∧ b * d ≤ L := by
  have hbd : b * d ≤ L := by simpa only [mul_comm] using (Nat.le_div_iff_mul_le hb).mp hd
  exact ⟨(Nat.mul_le_mul_right d hab).trans hbd, hbd⟩

theorem unsigned_pair_sum_eq {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    unsignedPairSum L a b = unsigned L a b := by
  rw [unsignedPairSum, unsigned, channel_sum_interval]
  apply sum_congr rfl
  intro d hd
  obtain ⟨haD, hbD⟩ := diameters_fit hb hab (mem_Icc.mp hd).2
  rw [placement_card haD, placement_card hbD, Nat.cast_sub (by omega : a * d ≤ L + 1),
    Nat.cast_sub (by omega : b * d ≤ L + 1)]
  push_cast
  ring

theorem signed_pair_sum_eq {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    signedPairSum L a b = signed L a b := by
  rw [signedPairSum, signed, channel_sum_interval]
  apply sum_congr rfl
  intro d hd
  obtain ⟨haD, hbD⟩ := diameters_fit hb hab (mem_Icc.mp hd).2
  rw [signed_placements haD, signed_placements hbD]
  push_cast
  ring

end PaperP1.ChannelPlacements
