module

public import PaperP1.Arithmetic.BoundedPointAlignment
public import PaperP1.Arithmetic.FixedChannelLinearCount

/-! # Two exact units determine a small positive reduced channel

The exact equations at both grid points are retained, not merely approximate
alignment of the window centers.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallExactUnitAlignment

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedUnitCount

theorem ordered_data (B : ℕ) (x y : ℤ) (p q : ℤ × ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y)
    (hp : |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ))
    (hq : |q.1| ≤ (B : ℤ) ∧ |q.2| ≤ (B : ℤ)) (hpq : p.1 < q.1)
    (hcross : (q.1 - p.1) * (y - p.2) = (q.2 - p.2) * (x - p.1)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * B ∧ b ≤ 2 * B ∧
      (b : ℤ) * (x - p.1) = (a : ℤ) * (y - p.2) ∧
      (b : ℤ) * (x - q.1) = (a : ℤ) * (y - q.2) := by
  have hxp : 0 < x - p.1 := by linarith [(abs_le.mp hp.1).2]
  have hyp : 0 < y - p.2 := by linarith [(abs_le.mp hp.2).2]
  have hdu : 0 < q.1 - p.1 := by omega
  have hdv : 0 < q.2 - p.2 := by
    have hpos : 0 < (q.2 - p.2) * (x - p.1) := by rw [← hcross]; exact mul_pos hdu hyp
    by_contra h
    have hnon : q.2 - p.2 ≤ 0 := by omega
    have hn := mul_nonpos_of_nonpos_of_nonneg hnon hxp.le
    omega
  let A := (q.1 - p.1).toNat
  let D := (q.2 - p.2).toNat
  have hAcast : (A : ℤ) = q.1 - p.1 := Int.toNat_of_nonneg hdu.le
  have hDcast : (D : ℤ) = q.2 - p.2 := Int.toNat_of_nonneg hdv.le
  have hA : 0 < A := by exact_mod_cast (show (0 : ℤ) < A by rw [hAcast]; exact hdu)
  have hD : 0 < D := by exact_mod_cast (show (0 : ℤ) < D by rw [hDcast]; exact hdv)
  have hAbound : A ≤ 2 * B := by
    have hi : (A : ℤ) ≤ ((2 * B : ℕ) : ℤ) := by
      rw [hAcast]
      push_cast
      linarith [(abs_le.mp hp.1).1, (abs_le.mp hq.1).2]
    exact_mod_cast hi
  have hDbound : D ≤ 2 * B := by
    have hi : (D : ℤ) ≤ ((2 * B : ℕ) : ℤ) := by
      rw [hDcast]
      push_cast
      linarith [(abs_le.mp hp.2).1, (abs_le.mp hq.2).2]
    exact_mod_cast hi
  let g := Nat.gcd A D
  let a := A / g
  let b := D / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left D hA
  have ha : 0 < a := Nat.div_pos (Nat.gcd_le_left D hA) hg
  have hb : 0 < b := Nat.div_pos (Nat.gcd_le_right A hD) hg
  have hcop : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  have hAg : (g : ℤ) * a = A := by exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left A D)
  have hDg : (g : ℤ) * b = D := by exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right A D)
  have hred : (b : ℤ) * (x - p.1) = (a : ℤ) * (y - p.2) := by
    apply mul_left_cancel₀ (by exact_mod_cast hg.ne' : (g : ℤ) ≠ 0)
    calc
      (g : ℤ) * ((b : ℤ) * (x - p.1)) = (D : ℤ) * (x - p.1) := by rw [← mul_assoc, hDg]
      _ = (A : ℤ) * (y - p.2) := by rw [hAcast, hDcast]; exact hcross.symm
      _ = (g : ℤ) * ((a : ℤ) * (y - p.2)) := by rw [← mul_assoc, hAg]
  have hdiff : (b : ℤ) * (q.1 - p.1) = (a : ℤ) * (q.2 - p.2) := by
    rw [← hAcast, ← hDcast, ← hAg, ← hDg]
    ring
  exact ⟨a, b, ha, hb, hcop, (Nat.div_le_self A g).trans hAbound,
    (Nat.div_le_self D g).trans hDbound, hred, by nlinarith only [hred, hdiff]⟩

theorem exact_data (B : ℕ) (x y : ℤ) (p q : ℤ × ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y)
    (hp : |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ))
    (hq : |q.1| ≤ (B : ℤ) ∧ |q.2| ≤ (B : ℤ)) (hpq : p ≠ q)
    (hcross : (q.1 - p.1) * (y - p.2) = (q.2 - p.2) * (x - p.1)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * B ∧ b ≤ 2 * B ∧
      (b : ℤ) * (x - p.1) = (a : ℤ) * (y - p.2) ∧
      (b : ℤ) * (x - q.1) = (a : ℤ) * (y - q.2) := by
  have hne : p.1 ≠ q.1 := by
    intro he
    have hxp : x - p.1 ≠ 0 := by linarith [(abs_le.mp hp.1).2]
    have hz : (q.2 - p.2) * (x - p.1) = 0 := by simpa only [he, sub_self, zero_mul] using hcross.symm
    have he₂ : q.2 = p.2 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hxp)
    exact hpq (Prod.ext he he₂.symm)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ordered_data B x y p q hx hy hp hq h hcross
  · have hswap : (p.1 - q.1) * (y - q.2) = (p.2 - q.2) * (x - q.1) := by nlinarith only [hcross]
    obtain ⟨a, b, ha, hb, hcop, haB, hbB, hq, hp⟩ := ordered_data B x y q p hx hy hq hp h hswap
    exact ⟨a, b, ha, hb, hcop, haB, hbB, hp, hq⟩

theorem two_units (x y L : ℕ) (hx : L + 1 < x) (hy : L + 1 < y)
    (u₁ u₂ v₁ v₂ : Fin (L + 1)) (hne : (u₁, v₁) ≠ (u₂, v₂))
    (he : startCompleteVertexLabel x L u₁ * startCompleteVertexLabel y L v₂ =
      startCompleteVertexLabel x L u₂ * startCompleteVertexLabel y L v₁) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * (L + 1) ∧ b ≤ 2 * (L + 1) ∧
      (u₁, v₁) ∈ units a b x y L ∧ (u₂, v₂) ∈ units a b x y L := by
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hpq : (-offset u₁, -offset v₁) ≠ (-offset u₂, -offset v₂) := by
    intro hh
    exact hne (Prod.ext (offset_injective L (neg_injective (congrArg Prod.fst hh)))
      (offset_injective L (neg_injective (congrArg Prod.snd hh))))
  have hcross : ((-offset u₂) - (-offset u₁)) * ((y : ℤ) - (-offset v₁)) =
      ((-offset v₂) - (-offset v₁)) * ((x : ℤ) - (-offset u₁)) := by
    have hz : (startCompleteVertexLabel x L u₁ : ℤ) * (startCompleteVertexLabel y L v₂ : ℤ) =
        (startCompleteVertexLabel x L u₂ : ℤ) * (startCompleteVertexLabel y L v₁ : ℤ) := by exact_mod_cast he
    rw [label_cast hxpos, label_cast hxpos, label_cast hypos, label_cast hypos] at hz
    nlinarith only [hz]
  obtain ⟨a, b, ha, hb, hcop, haB, hbB, hp, hq⟩ := exact_data (L + 1) x y
    (-offset u₁, -offset v₁) (-offset u₂, -offset v₂)
    (by exact_mod_cast hx) (by exact_mod_cast hy)
    ⟨by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs u₁,
      by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs v₁⟩
    ⟨by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs u₂,
      by simpa only [abs_neg] using EnlargedPairGeometry.offset_abs v₂⟩ hpq hcross
  have hunit (u v : Fin (L + 1)) (hh : (b : ℤ) * ((x : ℤ) - (-offset u)) =
      (a : ℤ) * ((y : ℤ) - (-offset v))) : (u, v) ∈ units a b x y L := by
    apply mem_units.mpr
    have hz : (b : ℤ) * (startCompleteVertexLabel x L u : ℤ) =
        (a : ℤ) * (startCompleteVertexLabel y L v : ℤ) := by
      simpa only [label_cast hxpos, label_cast hypos, sub_neg_eq_add] using hh
    exact_mod_cast hz
  exact ⟨a, b, ha, hb, hcop, haB, hbB, hunit u₁ v₁ hp, hunit u₂ v₂ hq⟩

end PaperP1.SmallExactUnitAlignment
