module

public import PaperP1.Arithmetic.ChannelSumIdentity

/-! # Exact positive two-to-three channel, with B=L+1 modulo three -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.TwoThreePositiveParity

open PaperP1.ChannelSumIdentity

theorem unsigned_B_zero {k : ℕ} (hk : 2 ≤ k) :
    unsigned (3 * k - 1) 2 3 =
      (2 : ℤ) ^ (k - 1) * (3 * k + 18) - 15 * k - 6 := by
  have hdiv : (3 * k - 1) / 3 = k - 1 := by omega
  have hL : ((3 * k - 1 : ℕ) : ℤ) = 3 * (k - 1 : ℕ) + 2 := by omega
  have hp : (2 : ℤ) ^ (k - 1) = 2 * (2 : ℤ) ^ (k - 1 - 1) := by
    have he : k - 1 = (k - 1 - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  unfold unsigned
  simp only [Nat.cast_ofNat]
  rw [hdiv, channel_identity (by omega : 1 ≤ k - 1) _ _ _ 2 _ hL]
  rw [hL, hp, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  push_cast
  ring

theorem unsigned_B_one {k : ℕ} (hk : 1 ≤ k) :
    unsigned (3 * k) 2 3 =
      (2 : ℤ) ^ (k - 1) * (4 * k + 24) - 15 * k - 11 := by
  have hdiv : (3 * k) / 3 = k := by omega
  unfold unsigned
  rw [hdiv, channel_identity hk _ _ _ 0 _ (by push_cast; ring)]
  push_cast
  ring

theorem unsigned_B_two {k : ℕ} (hk : 1 ≤ k) :
    unsigned (3 * k + 1) 2 3 =
      (2 : ℤ) ^ (k - 1) * (5 * k + 32) - 15 * k - 16 := by
  have hdiv : (3 * k + 1) / 3 = k := by omega
  unfold unsigned
  rw [hdiv, channel_identity hk _ _ _ 1 _ (by push_cast; ring)]
  push_cast
  ring

theorem unsigned_formula {k r : ℕ} (hk : 2 ≤ k) (hr : r < 3) :
    unsigned (3 * k + r - 1) 2 3 = (2 : ℤ) ^ (k - 1) *
      (((3 : ℤ) + r) * k + (r : ℤ) ^ 2 + 5 * r + 18) - 5 * (3 * k + r : ℕ) - 6 := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hr' with rfl | rfl | rfl
  · simp only [Nat.cast_zero, add_zero, mul_zero, zero_pow (by omega : 2 ≠ 0)]
    rw [unsigned_B_zero hk]
    push_cast
    ring
  · have hL : 3 * k + 1 - 1 = 3 * k := by omega
    rw [hL, unsigned_B_one (by omega : 1 ≤ k)]
    push_cast
    ring
  · have hL : 3 * k + 2 - 1 = 3 * k + 1 := by omega
    rw [hL, unsigned_B_two (by omega : 1 ≤ k)]
    push_cast
    ring

end PaperP1.TwoThreePositiveParity
