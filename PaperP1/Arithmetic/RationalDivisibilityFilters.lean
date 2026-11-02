module

public import PaperP1.Arithmetic.IntervalDivisibilityCount
public import PaperP1.Arithmetic.RationalTripleNormalizers

/-! # All coincidences with the third rational window lie in two fixed divisibility classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalDivisibilityFilters

open Finset PaperP1.NormalizedWindowSets PaperP1.IntervalDivisibilityCount
  PaperP1.FiniteEvenSquareClasses

theorem reduced_pos {u w : ℕ} (hu : 0 < u) (hw : 0 < w) : 0 < w / Nat.gcd u w :=
  Nat.div_pos (Nat.gcd_le_right u hw) (Nat.gcd_pos_of_pos_left w hu)

theorem reduced_dvd_iff {u w n : ℕ} (hu : 0 < u) :
    w / Nat.gcd u w ∣ n ↔ w ∣ u * n := by
  let g := Nat.gcd u w
  let a := u / g
  let b := w / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left w hu
  have hga : g * a = u := Nat.mul_div_cancel' (Nat.gcd_dvd_left u w)
  have hgb : g * b = w := Nat.mul_div_cancel' (Nat.gcd_dvd_right u w)
  have hcop : a.Coprime b := Nat.gcd_div_gcd_div_gcd_of_pos_left hu
  change b ∣ n ↔ w ∣ u * n
  rw [← hgb, ← hga, Nat.mul_assoc, Nat.mul_dvd_mul_iff_left hg]
  exact hcop.symm.dvd_mul_left.symm

theorem reduced_lcm {u v w : ℕ} (hprim : Nat.gcd (Nat.gcd u v) w = 1) :
    Nat.lcm (w / Nat.gcd u w) (w / Nat.gcd v w) = w := by
  rw [Nat.div_lcm_eq_div_gcd (Nat.gcd_dvd_right u w) (Nat.gcd_dvd_right v w),
    Nat.gcd_gcd_gcd_right, hprim, Nat.div_one]

theorem reduced_ratio {u w : ℕ} (hu : 0 < u) (hw : 0 < w) (B : ℝ) :
    B / (w / Nat.gcd u w : ℕ) = B * (Nat.gcd u w : ℝ) / w := by
  have hg : (0 : ℝ) < Nat.gcd u w := by exact_mod_cast Nat.gcd_pos_of_pos_left w hu
  have hb : (0 : ℝ) < (w / Nat.gcd u w : ℕ) := by exact_mod_cast reduced_pos hu hw
  have heq : (Nat.gcd u w : ℝ) * (w / Nat.gcd u w : ℕ) = w := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_right u w)
  rw [← heq]
  field_simp

theorem normalized_dvd {c x L n : ℕ} (hn : n ∈ normalized c x L) : c ∣ n := by
  obtain ⟨m, _, rfl⟩ := mem_image.mp hn
  exact Nat.dvd_mul_right _ _

theorem intersection_union_subset {u v w x y z L : ℕ} (hu : 0 < u) (hv : 0 < v) :
    (normalized (v * w) x L ∩ normalized (u * v) z L) ∪
        (normalized (u * w) y L ∩ normalized (u * v) z L) ⊆
      dilate (u * v) (hits (w / Nat.gcd u w) z L ∪ hits (w / Nat.gcd v w) z L) := by
  intro n hn
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp (mem_inter.mp hn).2
    have hdiv := normalized_dvd (mem_inter.mp hn).1
    rw [show (u * v) * m = v * (u * m) by ring] at hdiv
    have hwm : w ∣ u * m := (Nat.mul_dvd_mul_iff_left hv).mp hdiv
    exact mem_image.mpr ⟨m, mem_union_left _ (mem_filter.mpr ⟨hm, (reduced_dvd_iff hu).2 hwm⟩), rfl⟩
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp (mem_inter.mp hn).2
    have hdiv := normalized_dvd (mem_inter.mp hn).1
    rw [Nat.mul_assoc] at hdiv
    have hwm : w ∣ v * m := (Nat.mul_dvd_mul_iff_left hu).mp hdiv
    exact mem_image.mpr ⟨m, mem_union_right _ (mem_filter.mpr ⟨hm, (reduced_dvd_iff hv).2 hwm⟩), rfl⟩

theorem intersection_union_bound {u v w x y z L : ℕ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hz : 2 ≤ z) (hprim : Nat.gcd (Nat.gcd u v) w = 1) :
    (((normalized (v * w) x L ∩ normalized (u * v) z L) ∪
        (normalized (u * w) y L ∩ normalized (u * v) z L)).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * (Nat.gcd u w : ℝ) / w +
        ((L + 1 : ℕ) : ℝ) * (Nat.gcd v w : ℝ) / w - ((L + 1 : ℕ) : ℝ) / w + 3 := by
  have hcard := (card_le_card (intersection_union_subset (w := w) (x := x) (y := y) (z := z) (L := L) hu hv)).trans
    card_image_le
  have hcount := union_bound (L := L) (reduced_pos hu hw) (reduced_pos hv hw) hz
  rw [reduced_lcm hprim, reduced_ratio hu hw, reduced_ratio hv hw] at hcount
  refine le_trans ?_ hcount
  exact_mod_cast hcard

end PaperP1.RationalDivisibilityFilters
