module

public import PaperP1.Diophantine.IntegerLinearFibres
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # A divisor-grouped count for the actual congruence M divides n(n+h) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitQuadraticCongruences

open Finset

def quotientPair (M g h n : ℕ) : ℤ × ℤ := ((n / g : ℕ), ((n + h) / (M / g) : ℕ))

theorem gcd_quotient_divides (M n h : ℕ) (hM : 0 < M) (hroot : M ∣ n * (n + h)) :
    M / M.gcd n ∣ n + h := by
  have hz : (M : ℤ) ∣ (n : ℤ) * ((n + h : ℕ) : ℤ) := by exact_mod_cast hroot
  have hm : (n : ℤ) * ((n + h : ℕ) : ℤ) ≡ (n : ℤ) * 0 [ZMOD (M : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    simpa only [mul_zero, zero_sub] using dvd_neg.mpr hz
  have hc := hm.cancel_left_div_gcd (by exact_mod_cast hM : (0 : ℤ) < M)
  have hc' : ((n + h : ℕ) : ℤ) ≡ 0 [ZMOD ((M / M.gcd n : ℕ) : ℤ)] := by
    simpa only [Int.gcd_natCast_natCast, ← Int.natCast_div] using hc
  exact_mod_cast Int.modEq_zero_iff_dvd.mp hc'

theorem quotient_equation (M g h n : ℕ) (hM : 0 < M) (hroot : M ∣ n * (n + h))
    (hg : g = M.gcd n) : PaperP1.IntegerLinearFibres.Equation g (M / g) h (quotientPair M g h n) := by
  have hdivn : g ∣ n := by rw [hg]; exact Nat.gcd_dvd_right M n
  have hdivsum : M / g ∣ n + h := by rw [hg]; exact gcd_quotient_divides M n h hM hroot
  have hn : (g : ℤ) * (n / g : ℕ) = n := by exact_mod_cast Nat.mul_div_cancel' hdivn
  have hnh : ((M / g : ℕ) : ℤ) * ((n + h) / (M / g) : ℕ) = ((n + h : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hdivsum
  unfold PaperP1.IntegerLinearFibres.Equation quotientPair
  rw [hnh, hn, Nat.cast_add]
  ring

theorem quotientPair_injective (M g h : ℕ) (S : Finset ℕ) (hdiv : ∀ n ∈ S, g ∣ n) :
    Set.InjOn (quotientPair M g h) (↑S : Set ℕ) := by
  intro n hn m hm heq
  have hquot : n / g = m / g := by
    have h := congrArg Prod.fst heq
    change ((n / g : ℕ) : ℤ) = ((m / g : ℕ) : ℤ) at h
    exact_mod_cast h
  have hnrec := Nat.div_mul_cancel (hdiv n hn)
  have hmrec := Nat.div_mul_cancel (hdiv m hm)
  rw [hquot] at hnrec
  omega

theorem gcd_fibre_count (M X h : ℕ) (hM : 0 < M) (hh : 0 < h) (S : Finset ℕ)
    (hbox : ∀ n ∈ S, 0 < n ∧ n ≤ X) (hroot : ∀ n ∈ S, M ∣ n * (n + h))
    (g : ℕ) (hg : g ∈ S.image fun n ↦ M.gcd n) :
    ((S.filter fun n ↦ M.gcd n = g).card : ℝ) ≤ (X : ℝ) / M * h + 1 := by
  obtain ⟨n₀, hn₀, rfl⟩ := mem_image.mp hg
  let g := M.gcd n₀
  let T := S.filter fun n ↦ M.gcd n = g
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left n₀ hM
  have hmpos : 0 < M / g := Nat.div_pos (Nat.gcd_le_left n₀ hM) hgpos
  have hdiv : ∀ n ∈ T, g ∣ n := by
    intro n hn
    rw [← (mem_filter.mp hn).2]
    exact Nat.gcd_dvd_right M n
  have hprod : (g : ℝ) * (M / g : ℕ) = M := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.gcd_dvd_left M n₀)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hphysical : (X : ℝ) ≤ ((X : ℝ) / M) * (g : ℝ) * (M / g : ℕ) := by
    rw [mul_assoc, hprod]
    exact (div_mul_cancel₀ _ hMr.ne').ge
  classical
  have hcard := card_image_iff.mpr (quotientPair_injective M g h T hdiv)
  change (T.card : ℝ) ≤ _
  rw [← hcard]
  have heq : ∀ z ∈ T.image (quotientPair M g h), PaperP1.IntegerLinearFibres.Equation g (M / g) h z := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    exact quotient_equation M g h n hM (hroot n (mem_filter.mp hn).1) (mem_filter.mp hn).2.symm
  have hpos : ∀ z ∈ T.image (quotientPair M g h), 0 < z.1 := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    have hnpos := (hbox n (mem_filter.mp hn).1).1
    have hdivpos : 0 < n / g := Nat.div_pos (Nat.le_of_dvd hnpos (hdiv n hn)) hgpos
    change (0 : ℤ) < (n / g : ℕ)
    exact_mod_cast hdivpos
  have hheight : ∀ z ∈ T.image (quotientPair M g h), (g : ℝ) * z.1 ≤ (1 : ℝ) * X := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    change (g : ℝ) * ((n / g : ℕ) : ℤ) ≤ (1 : ℝ) * X
    norm_cast
    rw [one_mul, Nat.mul_div_cancel' (hdiv n hn)]
    exact (hbox n (mem_filter.mp hn).1).2
  have hb := PaperP1.IntegerLinearFibres.weighted_height_count g (M / g) hgpos hmpos h
    (by exact_mod_cast hh.ne' : (h : ℤ) ≠ 0) X ((X : ℝ) / M) 1
    (Nat.cast_nonneg X) (by positivity) (by norm_num) hphysical _ heq hpos hheight
  simpa only [mul_one, Int.natAbs_natCast] using hb

theorem root_count (M X h : ℕ) (hM : 0 < M) (hh : 0 < h) (S : Finset ℕ)
    (hbox : ∀ n ∈ S, 0 < n ∧ n ≤ X) (hroot : ∀ n ∈ S, M ∣ n * (n + h)) :
    (S.card : ℝ) ≤ (M.divisors.card : ℝ) * ((X : ℝ) / M * h + 1) := by
  have hsub : S.image (fun n ↦ M.gcd n) ⊆ M.divisors := by
    intro g hg
    obtain ⟨n, _, rfl⟩ := mem_image.mp hg
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left M n, hM.ne'⟩
  have hc := card_le_card hsub
  calc
    (S.card : ℝ) = ∑ g ∈ S.image (fun n ↦ M.gcd n), ((S.filter fun n ↦ M.gcd n = g).card : ℝ) := by
      have h := congrArg (fun m : ℕ ↦ (m : ℝ)) (card_eq_sum_card_image (fun n ↦ M.gcd n) S)
      simpa only [Nat.cast_sum] using h
    _ ≤ ∑ _g ∈ S.image (fun n ↦ M.gcd n), ((X : ℝ) / M * h + 1) := by
      apply sum_le_sum
      intro g hg
      exact gcd_fibre_count M X h hM hh S hbox hroot g hg
    _ = ((S.image (fun n ↦ M.gcd n)).card : ℝ) * ((X : ℝ) / M * h + 1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)

end PaperP1.SplitQuadraticCongruences
