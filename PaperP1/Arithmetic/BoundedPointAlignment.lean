module

public import PaperP1.Arithmetic.CompressedTargetAlignment
public import Mathlib.Tactic.FieldSimp

/-! # Two bounded collinear points force a positive reduced alignment at a distant center -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedPointAlignment

theorem ordered_alignment (B : ℕ) (x y : ℤ) (p q : ℤ × ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y)
    (hp : |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ))
    (hq : |q.1| ≤ (B : ℤ) ∧ |q.2| ≤ (B : ℤ)) (hpq : p.1 < q.1)
    (hcross : (q.1 - p.1) * (y - p.2) = (q.2 - p.2) * (x - p.1)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * B ∧ b ≤ 2 * B ∧
      |(b : ℤ) * x - (a : ℤ) * y| ≤ ((a + b : ℕ) : ℤ) * B := by
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
  have heq : (b : ℤ) * x - (a : ℤ) * y = (b : ℤ) * p.1 - (a : ℤ) * p.2 := by nlinarith [hred]
  refine ⟨a, b, ha, hb, hcop, (Nat.div_le_self A g).trans hAbound,
    (Nat.div_le_self D g).trans hDbound, ?_⟩
  calc
    |(b : ℤ) * x - (a : ℤ) * y| = |(b : ℤ) * p.1 - (a : ℤ) * p.2| := congrArg abs heq
    _ ≤ |(b : ℤ) * p.1| + |(a : ℤ) * p.2| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le ((b : ℤ) * p.1) 0 ((a : ℤ) * p.2)
    _ = (b : ℤ) * |p.1| + (a : ℤ) * |p.2| := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b), abs_of_nonneg (Nat.cast_nonneg (α := ℤ) a)]
    _ ≤ (b : ℤ) * B + (a : ℤ) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hp.1 (Nat.cast_nonneg b))
        (mul_le_mul_of_nonneg_left hp.2 (Nat.cast_nonneg a))
    _ = ((a + b : ℕ) : ℤ) * B := by push_cast; ring

theorem alignment_of_cross (B : ℕ) (x y : ℤ) (p q : ℤ × ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y)
    (hp : |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ))
    (hq : |q.1| ≤ (B : ℤ) ∧ |q.2| ≤ (B : ℤ)) (hpq : p ≠ q)
    (hcross : (q.1 - p.1) * (y - p.2) = (q.2 - p.2) * (x - p.1)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * B ∧ b ≤ 2 * B ∧
      |(b : ℤ) * x - (a : ℤ) * y| ≤ ((a + b : ℕ) : ℤ) * B := by
  have hne : p.1 ≠ q.1 := by
    intro he
    have hxp : x - p.1 ≠ 0 := by linarith [(abs_le.mp hp.1).2]
    have hz : (q.2 - p.2) * (x - p.1) = 0 := by simpa only [he, sub_self, zero_mul] using hcross.symm
    have he₂ : q.2 = p.2 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hxp)
    exact hpq (Prod.ext he he₂.symm)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ordered_alignment B x y p q hx hy hp hq h hcross
  · have hswap : (p.1 - q.1) * (y - q.2) = (p.2 - q.2) * (x - q.1) := by nlinarith [hcross]
    exact ordered_alignment B x y q p hx hy hq hp h hswap

theorem source_alignment {x y L : ℕ} (hL : 1 ≤ L)
    (hdata : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * (L + 1) ∧ b ≤ 2 * (L + 1) ∧
      |(b : ℤ) * x - (a : ℤ) * y| ≤ ((a + b : ℕ) : ℤ) * (L + 1)) :
    CompressedTargetAlignment.Aligned 1 x y L := by
  obtain ⟨a, b, ha, hb, hcop, haB, hbB, he⟩ := hdata
  have hsquare : 2 * (L + 1) ≤ (L + 1) ^ 2 := by nlinarith
  have hcube : (L + 1) ^ 2 ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨a, b, ha, hb, hcop, haB.trans (hsquare.trans hcube), hbB.trans (hsquare.trans hcube), ?_⟩
  simpa only [abs_sub_comm, one_mul, Nat.cast_add, Nat.cast_one] using he

end PaperP1.BoundedPointAlignment
