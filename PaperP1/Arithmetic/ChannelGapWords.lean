module

public import PaperP1.Arithmetic.ChannelPlacements
public import PaperP1.Affine.Characters

/-! # The exact A_d count and predecessor sign of a word with selected extreme units -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelGapWords

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ChannelPlacements PaperP1.ChannelSelectionCount

local instance channelGapWordPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Words (d : ℕ) :=
  {w : Fin (d + 1) → F₂ // w 0 = 1 ∧ w (Fin.last d) = 1 ∧ ∑ k, w k = 0}

instance wordsFintype (d : ℕ) : Fintype (Words d) := by unfold Words; infer_instance

theorem word_card {d : ℕ} (hd : 0 < d) : Fintype.card (Words d) = 2 ^ (d - 2) := by
  cases d with
  | zero => omega
  | succ m => exact endpoint_card m

theorem weight_eq_word_card {d : ℕ} (hd : 0 < d) :
    ChannelSumIdentity.weight d = (Fintype.card (Words d) : ℤ) := by
  cases d with
  | zero => omega
  | succ m => exact weight_eq_endpoint_card m

theorem root_parity {d a : ℕ} (ha : 0 < a) (i : ℕ) (w : Fin (d + 1) → F₂) (hroot : w 0 = 1) :
    (∑ k : Fin (d + 1), w k * if i + a * k.val = 0 then 1 else 0) = if i = 0 then 1 else 0 := by
  have heq (k : Fin (d + 1)) : i + a * k.val = 0 ↔ i = 0 ∧ k = 0 := by
    simp only [Nat.add_eq_zero_iff, Nat.mul_eq_zero, ha.ne', false_or, Fin.ext_iff, Fin.val_zero]
  simp_rw [heq]
  by_cases hi : i = 0
  · simp [hi, hroot, mul_ite]
  · simp [hi]

theorem word_sign {d a b : ℕ} (ha : 0 < a) (hb : 0 < b) (i j : ℕ) (w : Words d) :
    binarySign ((∑ k : Fin (d + 1), w.val k * if i + a * k.val = 0 then 1 else 0) +
      (∑ k : Fin (d + 1), w.val k * if j + b * k.val = 0 then 1 else 0)) =
      placementSign i * placementSign j := by
  rw [root_parity ha i w.val w.property.1, root_parity hb j w.val w.property.1, binarySign_add]
  have hsign (k : ℕ) : binarySign (if k = 0 then 1 else 0) = placementSign k := by
    by_cases hk : k = 0 <;> simp [hk, binarySign, placementSign]
  rw [hsign, hsign]

theorem total_word_sign {d a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (i j : ℕ) :
    (∑ w : Words d,
      binarySign ((∑ k : Fin (d + 1), w.val k * if i + a * k.val = 0 then 1 else 0) +
        (∑ k : Fin (d + 1), w.val k * if j + b * k.val = 0 then 1 else 0))) =
      ChannelSumIdentity.weight d * placementSign i * placementSign j := by
  simp_rw [word_sign ha hb i j]
  rw [sum_const, nsmul_eq_mul, card_univ, ← weight_eq_word_card hd]
  ring

end PaperP1.ChannelGapWords
