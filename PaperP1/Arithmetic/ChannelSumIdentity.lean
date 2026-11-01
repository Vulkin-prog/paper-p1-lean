module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! # Exact finite channel sums, arbitrary shifts and the empty-sum boundary -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.ChannelSumIdentity

open Finset

/-- For positive d, A₁=1 and A_d=2^(d-2) for d>=2; d=0 is never summed. -/
def weight (d : ℕ) : ℤ := if d = 1 then 1 else (2 : ℤ) ^ (d - 2)

def moment (m k : ℕ) : ℤ := ∑ d ∈ range m, weight (d + 1) * ((d + 1 : ℕ) : ℤ) ^ k

def channelSum (L a b s : ℤ) (m : ℕ) : ℤ :=
  ∑ d ∈ range m, weight (d + 1) * (L + s - a * ((d + 1 : ℕ) : ℤ)) *
    (L + s - b * ((d + 1 : ℕ) : ℤ))

def unsigned (L a b : ℕ) : ℤ := channelSum L a b 1 (L / b)

def signed (L a b : ℕ) : ℤ := channelSum L a b (-1) (L / b)

theorem weight_one : weight 1 = 1 := by norm_num [weight]

theorem weight_succ {m : ℕ} (hm : 1 ≤ m) : weight (m + 1) = (2 : ℤ) ^ (m - 1) := by
  have hne : m + 1 ≠ 1 := by omega
  have heq : m + 1 - 2 = m - 1 := by omega
  rw [weight, ite_eq_right hne, heq]

theorem moment_succ (m k : ℕ) :
    moment (m + 1) k = moment m k + weight (m + 1) * ((m + 1 : ℕ) : ℤ) ^ k := by
  exact sum_range_succ _ _

theorem moments {m : ℕ} (hm : 1 ≤ m) :
    moment m 0 = (2 : ℤ) ^ (m - 1) ∧
    moment m 1 = ((m : ℤ) - 1) * (2 : ℤ) ^ (m - 1) + 1 ∧
    moment m 2 = ((m : ℤ) ^ 2 - 2 * m + 3) * (2 : ℤ) ^ (m - 1) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [moment, weight]
  | succ m hm ih =>
    have hpow : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
      calc
        _ = (2 : ℤ) ^ ((m - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_succ]; ring
    have hsub : m + 1 - 1 = m := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [moment_succ, weight_succ hm, ih.1, hsub, hpow]
      ring
    · rw [moment_succ, weight_succ hm, ih.2.1, hsub, hpow]
      push_cast
      ring
    · rw [moment_succ, weight_succ hm, ih.2.2, hsub, hpow]
      push_cast
      ring

theorem sum_moments (L a b s : ℤ) (m : ℕ) :
    channelSum L a b s m = (L + s) ^ 2 * moment m 0 -
      (a + b) * (L + s) * moment m 1 + a * b * moment m 2 := by
  unfold channelSum moment
  simp only [Finset.mul_sum]
  rw [← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  ring

theorem channel_identity {m : ℕ} (hm : 1 ≤ m) (L a b r s : ℤ) (hL : L = b * m + r) :
    channelSum L a b s m = (2 : ℤ) ^ (m - 1) *
      ((b - a) * (b + r + s) * m + (r + s) ^ 2 + (a + b) * (r + s) + 3 * a * b) -
      (a + b) * (L + s) - a * b := by
  obtain ⟨h₀, h₁, h₂⟩ := moments hm
  rw [sum_moments, h₀, h₁, h₂, hL]
  ring

theorem empty_sum (L a b s : ℤ) : channelSum L a b s 0 = 0 := by simp [channelSum]

theorem positive_interval_sum (f : ℕ → ℤ) (m : ℕ) :
    (∑ d ∈ range m, f (d + 1)) = ∑ d ∈ Icc 1 m, f d := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, sum_Icc_succ_top (by omega), ih]

theorem channel_sum_interval (L a b s : ℤ) (m : ℕ) :
    channelSum L a b s m = ∑ d ∈ Icc 1 m, weight d * (L + s - a * d) * (L + s - b * d) := by
  exact positive_interval_sum (fun d ↦ weight d * (L + s - a * d) * (L + s - b * d)) m

theorem euclidean_identity {L a b : ℕ} (hm : 1 ≤ L / b) (s : ℤ) :
    channelSum L a b s (L / b) = (2 : ℤ) ^ (L / b - 1) *
      (((b : ℤ) - a) * ((b : ℤ) + (L % b : ℕ) + s) * (L / b : ℕ) +
        (((L % b : ℕ) : ℤ) + s) ^ 2 + ((a : ℤ) + b) * (((L % b : ℕ) : ℤ) + s) + 3 * a * b) -
      ((a : ℤ) + b) * ((L : ℤ) + s) - a * b := by
  apply channel_identity hm
  exact_mod_cast (Nat.div_add_mod L b).symm

theorem unsigned_empty {L a b : ℕ} (hm : L / b = 0) : unsigned L a b = 0 := by
  rw [unsigned, hm, empty_sum]

theorem signed_empty {L a b : ℕ} (hm : L / b = 0) : signed L a b = 0 := by
  rw [signed, hm, empty_sum]

theorem signed_two_three {m r : ℕ} (hm : 1 ≤ m) (hr : r < 3) :
    signed (3 * m + r) 2 3 = (2 : ℤ) ^ (m - 1) *
      (((r : ℤ) + 2) * m + (r : ℤ) ^ 2 + 3 * r + 14) - 5 * (3 * m + r : ℕ) - 1 := by
  have hdiv : (3 * m + r) / 3 = m := by omega
  unfold signed
  rw [hdiv, channel_identity hm _ _ _ (r : ℤ) _ (by push_cast; ring)]
  push_cast
  ring

theorem signed_three_four {m r : ℕ} (hm : 1 ≤ m) (hr : r < 4) :
    signed (4 * m + r) 3 4 = (2 : ℤ) ^ (m - 1) *
      (((r : ℤ) + 3) * m + (r : ℤ) ^ 2 + 5 * r + 30) - 7 * (4 * m + r : ℕ) - 5 := by
  have hdiv : (4 * m + r) / 4 = m := by omega
  unfold signed
  rw [hdiv, channel_identity hm _ _ _ (r : ℤ) _ (by push_cast; ring)]
  push_cast
  ring

end PaperP1.ChannelSumIdentity
