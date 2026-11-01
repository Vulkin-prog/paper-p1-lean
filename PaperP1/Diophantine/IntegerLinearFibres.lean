module

public import PaperP1.Arithmetic.IntervalCongruence
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.GCD
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-! # Actual linear Diophantine fibres with their exact gcd step -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerLinearFibres

open Finset

def Equation (A B : ℕ) (h : ℤ) (z : ℤ × ℤ) : Prop :=
  (B : ℤ) * z.2 - (A : ℤ) * z.1 = h

theorem gcd_dvd_shift (A B : ℕ) (h : ℤ) (z : ℤ × ℤ) (hz : Equation A B h z) :
    ((B.gcd A : ℕ) : ℤ) ∣ h := by
  rw [← hz]
  exact dvd_sub (dvd_mul_of_dvd_left (by exact_mod_cast Nat.gcd_dvd_left B A) _)
    (dvd_mul_of_dvd_left (by exact_mod_cast Nat.gcd_dvd_right B A) _)

theorem common_residue (A B : ℕ) (hB : 0 < B) (h : ℤ) (x y : ℤ × ℤ)
    (hx : Equation A B h x) (hy : Equation A B h y) :
    x.1 ≡ y.1 [ZMOD ((B / B.gcd A : ℕ) : ℤ)] := by
  have hm : (A : ℤ) * x.1 ≡ (A : ℤ) * y.1 [ZMOD (B : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    refine ⟨y.2 - x.2, ?_⟩
    unfold Equation at hx hy
    linear_combination hx - hy
  have hcancel := hm.cancel_left_div_gcd (by exact_mod_cast hB : (0 : ℤ) < B)
  simpa only [Int.gcd_natCast_natCast, ← Int.natCast_div] using hcancel

theorem first_injective_on_solutions (A B : ℕ) (hB : 0 < B) (h : ℤ)
    (S : Finset (ℤ × ℤ)) (hS : ∀ z ∈ S, Equation A B h z) :
    Set.InjOn Prod.fst (↑S : Set (ℤ × ℤ)) := by
  intro x hx y hy hxy
  have hxq := hS x hx
  have hyq := hS y hy
  apply Prod.ext hxy
  have hprod : (B : ℤ) * x.2 = (B : ℤ) * y.2 := by
    unfold Equation at hxq hyq
    linear_combination hxq - hyq + (A : ℤ) * hxy
  exact mul_left_cancel₀ (by exact_mod_cast hB.ne' : (B : ℤ) ≠ 0) hprod

theorem interval_count (A B : ℕ) (hB : 0 < B) (h a b : ℤ) (hab : a ≤ b)
    (S : Finset (ℤ × ℤ)) (hS : ∀ z ∈ S, Equation A B h z)
    (hbox : ∀ z ∈ S, z.1 ∈ Finset.Ico a b) :
    (S.card : ℚ) ≤ ((b - a : ℤ) : ℚ) / (B / B.gcd A : ℕ) + 1 := by
  classical
  have hr : 0 < B / B.gcd A := Nat.div_pos (Nat.gcd_le_left A hB) (Nat.gcd_pos_of_pos_left A hB)
  by_cases hne : S.Nonempty
  · obtain ⟨v, hv⟩ := hne
    have hc : S.card ≤ ({x ∈ Finset.Ico a b | x ≡ v.1 [ZMOD ((B / B.gcd A : ℕ) : ℤ)]}).card := by
      apply card_le_card_of_injOn Prod.fst
      · intro z hz
        exact mem_filter.mpr ⟨hbox z hz, common_residue A B hB h z v (hS z hz) (hS v hv)⟩
      · exact first_injective_on_solutions A B hB h S hS
    have hcq : (S.card : ℚ) ≤ ({x ∈ Finset.Ico a b | x ≡ v.1 [ZMOD ((B / B.gcd A : ℕ) : ℤ)]}).card := by
      exact_mod_cast hc
    exact hcq.trans
      (PaperP1.Channels.card_Ico_modEq_cast_le_div_add_one a b v.1 _ (by exact_mod_cast hr) hab)
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    have hlength : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.mpr hab
    positivity

theorem positive_box_count (A B U : ℕ) (hB : 0 < B) (h : ℤ)
    (S : Finset (ℤ × ℤ)) (hS : ∀ z ∈ S, Equation A B h z)
    (hbox : ∀ z ∈ S, 0 < z.1 ∧ z.1 ≤ (U : ℤ)) :
    (S.card : ℝ) ≤ (U : ℝ) * (B.gcd A : ℕ) / B + 1 := by
  have hbase := interval_count A B hB h 1 ((U : ℤ) + 1) (by omega) S hS
    (fun z hz ↦ mem_Ico.mpr ⟨by have := (hbox z hz).1; omega, by have := (hbox z hz).2; omega⟩)
  have hc : (S.card : ℝ) ≤ (U : ℝ) / (B / B.gcd A : ℕ) + 1 := by
    have hq : (S.card : ℚ) ≤ (U : ℚ) / (B / B.gcd A : ℕ) + 1 := by
      simpa only [add_sub_cancel_right, Int.cast_natCast] using hbase
    have hcast : ((S.card : ℚ) : ℝ) ≤ (((U : ℚ) / (B / B.gcd A : ℕ) + 1 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hq
    push_cast at hcast
    exact hcast
  have hr : 0 < B / B.gcd A := Nat.div_pos (Nat.gcd_le_left A hB) (Nat.gcd_pos_of_pos_left A hB)
  have hprod : ((B / B.gcd A : ℕ) : ℝ) * (B.gcd A : ℕ) = B := by
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left B A)
  have heq : (U : ℝ) / (B / B.gcd A : ℕ) = (U : ℝ) * (B.gcd A : ℕ) / B := by
    apply (div_eq_div_iff (by exact_mod_cast hr.ne' : ((B / B.gcd A : ℕ) : ℝ) ≠ 0)
      (by exact_mod_cast hB.ne' : (B : ℝ) ≠ 0)).mpr
    rw [← hprod]
    ring
  rw [heq] at hc
  exact hc

theorem scaled_positive_count (A B U : ℕ) (hA : 0 < A) (hB : 0 < B) (h : ℤ) (hh : h ≠ 0)
    (N C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hheight : (U : ℝ) * A ≤ C₁ * N) (hproduct : N ≤ C₀ * (A : ℝ) * B)
    (S : Finset (ℤ × ℤ)) (hS : ∀ z ∈ S, Equation A B h z)
    (hbox : ∀ z ∈ S, 0 < z.1 ∧ z.1 ≤ (U : ℤ)) :
    (S.card : ℝ) ≤ C₀ * C₁ * h.natAbs + 1 := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  by_cases hne : S.Nonempty
  · obtain ⟨v, hv⟩ := hne
    have hdiv := Int.natAbs_dvd_natAbs.mpr (gcd_dvd_shift A B h v (hS v hv))
    simp only [Int.natAbs_natCast] at hdiv
    have hgn : B.gcd A ≤ h.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hh) hdiv
    have hg : ((B.gcd A : ℕ) : ℝ) ≤ h.natAbs := by exact_mod_cast hgn
    have hres : (U : ℝ) * A ≤ (C₀ * C₁ * B) * A := by
      calc
        _ ≤ C₁ * N := hheight
        _ ≤ C₁ * (C₀ * (A : ℝ) * B) := mul_le_mul_of_nonneg_left hproduct hC₁
        _ = _ := by ring
    have hu : (U : ℝ) ≤ C₀ * C₁ * B := (mul_le_mul_iff_left₀ hAr).mp (by nlinarith only [hres])
    calc
      (S.card : ℝ) ≤ (U : ℝ) * (B.gcd A : ℕ) / B + 1 := positive_box_count A B U hB h S hS hbox
      _ ≤ (C₀ * C₁ * B) * (B.gcd A : ℕ) / B + 1 := by
        exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg _)) hBr.le) (le_refl _)
      _ = C₀ * C₁ * (B.gcd A : ℕ) + 1 := by field_simp
      _ ≤ C₀ * C₁ * h.natAbs + 1 := add_le_add (mul_le_mul_of_nonneg_left hg (mul_nonneg hC₀ hC₁)) (le_refl _)
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    positivity

theorem weighted_height_count (A B : ℕ) (hA : 0 < A) (hB : 0 < B) (h : ℤ) (hh : h ≠ 0)
    (N C₀ C₁ : ℝ) (hN : 0 ≤ N) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hproduct : N ≤ C₀ * (A : ℝ) * B) (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, Equation A B h z)
    (hpos : ∀ z ∈ S, 0 < z.1)
    (hheight : ∀ z ∈ S, (A : ℝ) * z.1 ≤ C₁ * N) :
    (S.card : ℝ) ≤ C₀ * C₁ * h.natAbs + 1 := by
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  let X := C₁ * N / A
  have hX : 0 ≤ X := div_nonneg (mul_nonneg hC₁ hN) hAr.le
  have hfloor : (⌊X⌋₊ : ℝ) * A ≤ C₁ * N := by
    have hbound := mul_le_mul_of_nonneg_right (Nat.floor_le hX) hAr.le
    exact hbound.trans_eq (by dsimp [X]; field_simp)
  apply scaled_positive_count A B ⌊X⌋₊ hA hB h hh N C₀ C₁ hC₀ hC₁ hfloor hproduct S hS
  intro z hz
  have hzpos := hpos z hz
  have hzreal : (z.1 : ℝ) ≤ X := (le_div_iff₀ hAr).mpr (by simpa only [mul_comm] using hheight z hz)
  have habs : (z.1.natAbs : ℝ) = z.1 := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hzpos : (0 : ℝ) < z.1)]
  have hnat : z.1.natAbs ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr (by simpa only [habs] using hzreal)
  have hzbound : z.1 ≤ (⌊X⌋₊ : ℤ) := by
    have hh' : |z.1| ≤ (⌊X⌋₊ : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hnat
    exact (le_abs_self _).trans hh'
  exact ⟨hzpos, hzbound⟩

end PaperP1.IntegerLinearFibres
