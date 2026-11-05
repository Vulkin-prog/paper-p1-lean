module

public import PaperP1.Arithmetic.IntegerRealIntervalCount
public import Mathlib.Data.Int.ModEq
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Real.Sqrt

/-! # Divisor-grouped square congruences in a short square-value range

Grouping by gcd(M,z-base) gives a common residue modulo max(g,M/g).
Its square is at least M, yielding a square-root bound for each fibre.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareCongruenceRangeCount

open Finset

theorem common_residue_card (S : Finset ℤ) (hne : S.Nonempty) (L : ℕ) (hL : 0 < L)
    (hdiv : ∀ z ∈ S, (L : ℤ) ∣ z - S.min' hne) :
    (S.card : ℝ) ≤ ((S.max' hne : ℝ) - S.min' hne) / L + 1 := by
  let a := S.min' hne
  let b := S.max' hne
  let f : ℤ → ℤ := fun z ↦ (z - a) / L
  have hrec (z : ℤ) (hz : z ∈ S) : (L : ℤ) * f z = z - a := by
    exact Int.mul_ediv_cancel' (hdiv z hz)
  have hf : Set.InjOn f (S : Set ℤ) := by
    intro z hz w hw he
    have h := hrec z hz
    rw [he, hrec w hw] at h
    omega
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hab : (0 : ℝ) ≤ ((b : ℝ) - a) / L := by
    apply div_nonneg _ hLr.le
    exact_mod_cast sub_nonneg.mpr (S.min'_le_max' hne)
  have hcard := IntegerRealIntervalCount.interval_card (S.image f) 0
    (((b : ℝ) - a) / L) hab (by
      intro q hq
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hq
      have hlo : a ≤ z := S.min'_le z hz
      have hhi : z ≤ b := S.le_max' z hz
      have hrecR : (L : ℝ) * (f z : ℝ) = (z : ℝ) - a := by exact_mod_cast hrec z hz
      constructor
      · apply nonneg_of_mul_nonneg_right _ hLr
        rw [hrecR]
        exact_mod_cast sub_nonneg.mpr hlo
      · apply (le_div_iff₀ hLr).mpr
        rw [mul_comm, hrecR]
        exact_mod_cast sub_le_sub_right hhi a)
  simpa only [card_image_of_injOn hf, sub_zero] using hcard

def gcdColor (M : ℕ) (base z : ℤ) : ℕ := Int.gcd (M : ℤ) (z - base)

theorem color_dvd (M : ℕ) (base z : ℤ) : gcdColor M base z ∣ M := by
  have h := Int.gcd_dvd_left (M : ℤ) (z - base)
  exact_mod_cast h

theorem quotient_divides_sum (M : ℕ) (hM : 0 < M) (base z : ℤ)
    (hz : (M : ℤ) ∣ z ^ 2 - base ^ 2) :
    ((M / gcdColor M base z : ℕ) : ℤ) ∣ z + base := by
  have hprod : (M : ℤ) ∣ (z - base) * (z + base) := by
    convert hz using 1
    ring
  have hm : (z - base) * (z + base) ≡ (z - base) * 0 [ZMOD (M : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    simpa only [mul_zero, zero_sub] using dvd_neg.mpr hprod
  have hc := hm.cancel_left_div_gcd (by exact_mod_cast hM : (0 : ℤ) < M)
  have hc' : z + base ≡ 0 [ZMOD ((M / gcdColor M base z : ℕ) : ℤ)] := by
    simpa only [gcdColor, Int.natCast_div] using hc
  exact Int.modEq_zero_iff_dvd.mp hc'

theorem same_color_divides_difference (M : ℕ) (hM : 0 < M) (base z w : ℤ)
    (hz : (M : ℤ) ∣ z ^ 2 - base ^ 2) (hw : (M : ℤ) ∣ w ^ 2 - base ^ 2)
    (he : gcdColor M base z = gcdColor M base w) :
    ((max (gcdColor M base z) (M / gcdColor M base z) : ℕ) : ℤ) ∣ z - w := by
  let g := gcdColor M base z
  have hz1 : (g : ℤ) ∣ z - base := Int.gcd_dvd_right (M : ℤ) (z - base)
  have hw1 : (g : ℤ) ∣ w - base := by
    change (gcdColor M base z : ℤ) ∣ _
    rw [he]
    exact Int.gcd_dvd_right (M : ℤ) (w - base)
  have h1 : (g : ℤ) ∣ z - w := by
    convert dvd_sub hz1 hw1 using 1
    ring
  have hz2 : ((M / g : ℕ) : ℤ) ∣ z + base := quotient_divides_sum M hM base z hz
  have hw2 : ((M / g : ℕ) : ℤ) ∣ w + base := by
    change ((M / gcdColor M base z : ℕ) : ℤ) ∣ _
    rw [he]
    exact quotient_divides_sum M hM base w hw
  have h2 : ((M / g : ℕ) : ℤ) ∣ z - w := by
    convert dvd_sub hz2 hw2 using 1
    ring
  change ((max g (M / g) : ℕ) : ℤ) ∣ _
  rcases le_total g (M / g) with h | h
  · rw [max_eq_right h]
    exact h2
  · rw [max_eq_left h]
    exact h1

theorem fibre_card (M : ℕ) (hM : 0 < M) (base : ℤ) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset ℤ) (hpos : ∀ z ∈ S, 0 ≤ z)
    (hcong : ∀ z ∈ S, (M : ℤ) ∣ z ^ 2 - base ^ 2)
    (hrange : ∀ z ∈ S, ∀ w ∈ S, (z : ℝ) ^ 2 - (w : ℝ) ^ 2 ≤ (M : ℝ) * R)
    (g : ℕ) (hg : ∀ z ∈ S, gcdColor M base z = g) :
    (S.card : ℝ) ≤ Real.sqrt R + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [card_empty, Nat.cast_zero]
    positivity
  let v := S.min' hne
  have hv : v ∈ S := S.min'_mem hne
  have hgdiv : g ∣ M := by rw [← hg v hv]; exact color_dvd M base v
  have hgpos : 0 < g := by
    by_contra hn
    have hzero : g = 0 := by omega
    rw [hzero] at hgdiv
    have : M = 0 := zero_dvd_iff.mp hgdiv
    omega
  let L := max g (M / g)
  have hL : 0 < L := hgpos.trans_le (le_max_left _ _)
  have hprod : g * (M / g) = M := Nat.mul_div_cancel' hgdiv
  have hML : M ≤ L ^ 2 := by
    rw [← hprod, pow_two]
    exact Nat.mul_le_mul (le_max_left _ _) (le_max_right _ _)
  have hdiv : ∀ z ∈ S, (L : ℤ) ∣ z - S.min' hne := by
    intro z hz
    have h := same_color_divides_difference M hM base z (S.min' hne)
      (hcong z hz) (hcong _ (S.min'_mem hne))
      ((hg z hz).trans (hg _ (S.min'_mem hne)).symm)
    simpa only [hg z hz, L] using h
  have hcard := common_residue_card S hne L hL hdiv
  have hmin : (0 : ℝ) ≤ S.min' hne := by exact_mod_cast hpos _ (S.min'_mem hne)
  have horder : (S.min' hne : ℝ) ≤ S.max' hne := by exact_mod_cast S.min'_le_max' hne
  have hspan : ((S.max' hne : ℝ) - S.min' hne) ^ 2 ≤ (M : ℝ) * R := by
    have h := hrange _ (S.max'_mem hne) _ (S.min'_mem hne)
    nlinarith
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hMLr : (M : ℝ) ≤ (L : ℝ) ^ 2 := by exact_mod_cast hML
  have hratio : (((S.max' hne : ℝ) - S.min' hne) / L) ^ 2 ≤ R := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hLr)).mpr
    exact hspan.trans (by nlinarith [mul_le_mul_of_nonneg_right hMLr hR])
  exact hcard.trans (by linarith [Real.le_sqrt_of_sq_le hratio])

theorem nonnegative_count (M : ℕ) (hM : 0 < M) (base : ℤ) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset ℤ) (hpos : ∀ z ∈ S, 0 ≤ z)
    (hcong : ∀ z ∈ S, (M : ℤ) ∣ z ^ 2 - base ^ 2)
    (hrange : ∀ z ∈ S, ∀ w ∈ S, (z : ℝ) ^ 2 - (w : ℝ) ^ 2 ≤ (M : ℝ) * R) :
    (S.card : ℝ) ≤ (M.divisors.card : ℝ) * (Real.sqrt R + 1) := by
  have hsub : S.image (gcdColor M base) ⊆ M.divisors := by
    intro g hg
    obtain ⟨z, _hz, rfl⟩ := mem_image.mp hg
    exact Nat.mem_divisors.mpr ⟨color_dvd M base z, hM.ne'⟩
  have hcard : ((S.image (gcdColor M base)).card : ℝ) ≤ M.divisors.card := by
    exact_mod_cast card_le_card hsub
  calc
    (S.card : ℝ) = ∑ g ∈ S.image (gcdColor M base),
        ((S.filter (fun z ↦ gcdColor M base z = g)).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image (gcdColor M base) S
    _ ≤ ∑ _g ∈ S.image (gcdColor M base), (Real.sqrt R + 1) := by
      apply sum_le_sum
      intro g _hg
      apply fibre_card M hM base R hR
      · intro z hz
        exact hpos z (mem_filter.mp hz).1
      · intro z hz
        exact hcong z (mem_filter.mp hz).1
      · intro z hz w hw
        exact hrange z (mem_filter.mp hz).1 w (mem_filter.mp hw).1
      · intro z hz
        exact (mem_filter.mp hz).2
    _ = ((S.image (gcdColor M base)).card : ℝ) * (Real.sqrt R + 1) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem abs_card (S : Finset ℤ) : S.card ≤ 2 * (S.image abs).card := by
  have hfibre (t : ℤ) : (S.filter (fun z ↦ |z| = t)).card ≤ 2 := by
    have hsub : S.filter (fun z ↦ |z| = t) ⊆ {t, -t} := by
      intro z hz
      have he : z ^ 2 = t ^ 2 := by rw [← sq_abs z, (mem_filter.mp hz).2]
      simpa only [mem_insert, mem_singleton] using eq_or_eq_neg_of_sq_eq_sq z t he
    exact (card_le_card hsub).trans card_le_two
  calc
    S.card = ∑ t ∈ S.image abs, (S.filter (fun z ↦ |z| = t)).card :=
      card_eq_sum_card_image abs S
    _ ≤ ∑ _t ∈ S.image abs, 2 := sum_le_sum (fun t _ht ↦ hfibre t)
    _ = _ := by simp [Nat.mul_comm]

theorem signed_count (M : ℕ) (hM : 0 < M) (base : ℤ) (R : ℝ) (hR : 0 ≤ R)
    (S : Finset ℤ) (hcong : ∀ z ∈ S, (M : ℤ) ∣ z ^ 2 - base ^ 2)
    (hrange : ∀ z ∈ S, ∀ w ∈ S, (z : ℝ) ^ 2 - (w : ℝ) ^ 2 ≤ (M : ℝ) * R) :
    (S.card : ℝ) ≤ 2 * (M.divisors.card : ℝ) * (Real.sqrt R + 1) := by
  have habs := nonnegative_count M hM base R hR (S.image abs) (by
    intro z hz
    obtain ⟨w, _hw, rfl⟩ := mem_image.mp hz
    exact abs_nonneg w) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    simpa only [sq_abs] using hcong w hw) (by
    intro z hz w hw
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hw
    simpa only [Int.cast_abs, sq_abs] using hrange a ha b hb)
  have hc : (S.card : ℝ) ≤ 2 * ((S.image abs).card : ℝ) := by exact_mod_cast abs_card S
  exact hc.trans (by nlinarith)

end PaperP1.SquareCongruenceRangeCount
