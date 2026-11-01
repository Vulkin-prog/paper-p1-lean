module

public import PaperP1.Arithmetic.DyadicEndpointPairs
public import PaperP1.Model.CompatibleTargetMatches

/-! # Actual target counts outside a literal finite family of endpoint sources -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicMatchBound

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ActualNormalizedMatches PaperP1.FixedChannelGamma PaperP1.DyadicEndpointPairs

theorem ratio_outside_exceptional {N L x y z a b c d t H : ℕ} {h : ℤ} (hN : 0 < N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hd : 0 < d) (hdH : d ≤ H) (hh : |h| ≤ H)
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * H * ((L + 1) + 1)) + (L + 1) < N)
    (haway : (x, y) ∉ exceptional N a b L ((L + 1) + 2 * H)) :
    (b : ℚ) / 2 < (c : ℚ) / d ∧ (c : ℚ) / d < 2 * a := by
  have hnearNot : ¬(|(a : ℤ) * t - N| ≤ ((L + 1) + 2 * H : ℕ) ∨
      |(b : ℤ) * t - 2 * N| ≤ ((L + 1) + 2 * H : ℕ)) := by
    intro hnear
    exact haway (mem_exceptional_of_parameter hx hy i j hbaseX hbaseY hnear)
  have hawayA : ((L + 1 : ℕ) : ℤ) + 2 * H < |(a : ℤ) * t - N| := by
    have h : (((L + 1) + 2 * H : ℕ) : ℤ) < |(a : ℤ) * t - N| :=
      lt_of_not_ge (fun hn ↦ hnearNot (Or.inl hn))
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  have hawayB : ((L + 1 : ℕ) : ℤ) + 2 * H < |(b : ℤ) * t - 2 * N| := by
    have h : (((L + 1) + 2 * H : ℕ) : ℤ) < |(b : ℤ) * t - 2 * N| :=
      lt_of_not_ge (fun hn ↦ hnearNot (Or.inr hn))
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  exact ActualDyadicInterior.ratio_interior hN hx hy hz hd hdH hh i j hbaseX hbaseY
    htarget hsize hawayA hawayB

theorem separated_bound {N L x y z a b c d t H : ℕ} {h : ℤ} (hN : 0 < N)
    (ha : 0 < a) (hb : 3 ≤ b) (hab : a.Coprime b) (horder : a < b)
    (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hsepX : x + L ≤ z ∨ z + L ≤ x) (hsepY : y + L ≤ z ∨ z + L ≤ y)
    (hdH : d ≤ H) (hh : |h| ≤ H)
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * H * ((L + 1) + 1)) + (L + 1) < N)
    (haway : (x, y) ∉ exceptional N a b L ((L + 1) + 2 * H)) :
    ((exactOffsets a b c d x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * gammaReal a b + 3 := by
  obtain ⟨hlo, hhi⟩ := ratio_outside_exceptional hN hx hy hz hd hdH hh i j hbaseX hbaseY htarget hsize haway
  exact SeparatedTargetMatches.match_bound ha hb hab horder hc hd hcop
    (hN.trans_le (mem_Ico.mp hx).1) (hN.trans_le (mem_Ico.mp hy).1) (hN.trans_le (mem_Ico.mp hz).1)
    hsepX hsepY i j h hbaseX hbaseY htarget hlo hhi

theorem compatible_bound {N L x y z a b c d t H : ℕ} {h : ℤ} (hN : 0 < N)
    (ha : 0 < a) (hb : 3 ≤ b) (hab : a.Coprime b) (horder : a < b)
    (hc : 0 < c) (hd : 0 < d) (hcop : c.Coprime d)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hL : 0 < L) (hxz : x ≠ z) (hyz : y ≠ z) (hq : 0 < infiniteJointMoment L {x, y, z})
    (hdH : d ≤ H) (hh : |h| ≤ H)
    (i j : Fin (L + 1)) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (hbaseY : startCompleteVertexLabel y L j = b * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : a * (2 * H * ((L + 1) + 1)) + (L + 1) < N)
    (haway : (x, y) ∉ exceptional N a b L ((L + 1) + 2 * H)) :
    ((exactOffsets a b c d x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * gammaReal a b + 3 := by
  obtain ⟨hqx, hqy⟩ := CompatibleWindowOverlap.triple_joint_pairs hq
  have hsepX := CompatibleWindowOverlap.compatible_pair_separated hxz hL hqx
  have hsepY := CompatibleWindowOverlap.compatible_pair_separated hyz hL hqy
  exact separated_bound hN ha hb hab horder hc hd hcop hx hy hz hsepX hsepY
    hdH hh i j hbaseX hbaseY htarget hsize haway

end PaperP1.DyadicMatchBound
