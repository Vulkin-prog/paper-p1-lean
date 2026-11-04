module

public import PaperP1.Arithmetic.ChannelSumIdentity

/-! # Exact and distinct parity formulas for the leading one-to-two channel

The signed formula splits L. The positive formula splits B=L+1.
The even-B boundary is proved separately to retain the correct power.
-/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.OneTwoChannelParity

open PaperP1.ChannelSumIdentity

theorem signed_formula {m s : ℕ} (hm : 1 ≤ m) (hs : s < 2) :
    signed (2 * m + s) 1 2 = (2 : ℤ) ^ (m - 1) *
      (((s : ℤ) + 1) * m + (s : ℤ) ^ 2 + s + 4) - 3 * (2 * m + s : ℕ) + 1 := by
  have hdiv : (2 * m + s) / 2 = m := by omega
  unfold signed
  rw [hdiv, channel_identity hm _ _ _ (s : ℤ) _ (by push_cast; ring)]
  push_cast
  ring

theorem unsigned_odd_B {k : ℕ} (hk : 1 ≤ k) :
    unsigned (2 * k) 1 2 = (2 : ℤ) ^ (k - 1) * (3 * k + 10) - 6 * k - 5 := by
  have hdiv : (2 * k) / 2 = k := by omega
  unfold unsigned
  rw [hdiv, channel_identity hk _ _ _ 0 _ (by push_cast; ring)]
  push_cast
  ring

theorem unsigned_even_B {k : ℕ} (hk : 2 ≤ k) :
    unsigned (2 * k - 1) 1 2 = (2 : ℤ) ^ (k - 1) * (2 * k + 6) - 6 * k - 2 := by
  have hdiv : (2 * k - 1) / 2 = k - 1 := by omega
  have hL : ((2 * k - 1 : ℕ) : ℤ) = 2 * (k - 1 : ℕ) + 1 := by omega
  have hp : (2 : ℤ) ^ (k - 1) = 2 * (2 : ℤ) ^ (k - 1 - 1) := by
    have he : k - 1 = (k - 1 - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    ring
  unfold unsigned
  simp only [Nat.cast_ofNat]
  rw [hdiv, channel_identity (by omega : 1 ≤ k - 1) _ _ _ 1 _ hL]
  rw [hL, hp, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  push_cast
  ring


theorem unsigned_formula {k r : ℕ} (hk : 2 ≤ k) (hr : r < 2) :
    unsigned (2 * k + r - 1) 1 2 = (2 : ℤ) ^ (k - 1) *
      (((2 : ℤ) + r) * k + 6 + 4 * r) - 3 * (2 * k + r : ℕ) - 2 := by
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases hr' with rfl | rfl
  · simp only [Nat.cast_zero, add_zero, mul_zero]
    rw [unsigned_even_B hk]
    push_cast
    ring
  · have hL : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hL, unsigned_odd_B (by omega : 1 ≤ k)]
    push_cast
    ring

end PaperP1.OneTwoChannelParity
