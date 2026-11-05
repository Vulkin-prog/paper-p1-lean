module

public import PaperP1.Arithmetic.OrdinarySmoothCensus
public import PaperP1.Arithmetic.DyadicOddPivots

/-! # A finite positive-density transfer to an actual dyadic smooth population

Only a fixed initial fraction of the full interval is discarded. The remaining
doubling exponents are bounded by a fixed integer, giving fixed multiplicity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySmoothDyadicDensity

open Finset OrdinarySmoothCensus OddPrimePivot DyadicOddPivots

def dyadicSmooth (N Y : ℕ) : Finset ℕ := (Ico N (2 * N)).filter fun n ↦ largestPrimeFactor n ≤ Y

theorem multiply_two_pow {n Y : ℕ} (hn : 0 < n) (hY : 2 ≤ Y)
    (hs : largestPrimeFactor n ≤ Y) (j : ℕ) : largestPrimeFactor (2 ^ j * n) ≤ Y := by
  induction j with
  | zero => simpa only [pow_zero, one_mul] using hs
  | succ j ih =>
    have he : 2 ^ (j + 1) * n = 2 * (2 ^ j * n) := by rw [pow_succ]; ring
    rw [he, largestPrimeFactor_mul (by decide : (2 : ℕ) ≠ 0) (by positivity),
      largestPrimeFactor_prime Nat.prime_two]
    exact max_le hY ih

theorem image_mem {N Y n : ℕ} (hN : 0 < N) (hY : 2 ≤ Y) (hn : n ∈ smoothUpTo N Y) :
    dyadicImage N n ∈ dyadicSmooth N Y := by
  obtain ⟨hn1, hnx, hny⟩ := mem_smoothUpTo.mp hn
  refine mem_filter.mpr ⟨dyadicImage_mem hN (mem_Icc.mpr ⟨hn1, hnx⟩), ?_⟩
  exact multiply_two_pow (by omega) hY hny _

theorem exponent_le {N n J : ℕ} (hn : 1 ≤ n) (hcap : N ≤ 2 ^ J * n) :
    doublingExponent N n ≤ J := by
  apply Nat.find_min'
  simpa only [max_eq_right hn] using hcap

theorem paired_image_injective (N : ℕ) :
    Function.Injective (fun n : ℕ ↦ (doublingExponent N n, dyadicImage N n)) := by
  intro n m h
  have he := congrArg Prod.fst h
  have hi := congrArg Prod.snd h
  change doublingExponent N n = doublingExponent N m at he
  change 2 ^ doublingExponent N n * n = 2 ^ doublingExponent N m * m at hi
  rw [he] at hi
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ doublingExponent N m) hi

theorem finite_transfer (N Y J : ℕ) (hN : 0 < N) (hY : 2 ≤ Y) :
    (smoothUpTo N Y).card ≤ N / 2 ^ J + (J + 1) * (dyadicSmooth N Y).card := by
  let U := (smoothUpTo N Y).filter fun n ↦ N ≤ 2 ^ J * n
  have hcover : smoothUpTo N Y ⊆ Icc 1 (N / 2 ^ J) ∪ U := by
    intro n hn
    obtain ⟨hn1, _, _⟩ := mem_smoothUpTo.mp hn
    by_cases hcap : N ≤ 2 ^ J * n
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, hcap⟩)
    · apply mem_union_left
      apply mem_Icc.mpr
      refine ⟨hn1, (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ J)).mpr ?_⟩
      nlinarith only [hcap]
  have hupper : U.card ≤ (J + 1) * (dyadicSmooth N Y).card := by
    have hh : U.card ≤ ((range (J + 1)) ×ˢ dyadicSmooth N Y).card := by
      apply card_le_card_of_injOn (fun n ↦ (doublingExponent N n, dyadicImage N n))
      · intro n hn
        obtain ⟨hs, hcap⟩ := mem_filter.mp hn
        have hn1 := (mem_smoothUpTo.mp hs).1
        exact mem_product.mpr ⟨mem_range.mpr (by change doublingExponent N n < J + 1; have := exponent_le hn1 hcap; omega), image_mem hN hY hs⟩
      · exact fun n _ m _ he ↦ paired_image_injective N he
    simpa only [card_product, card_range] using hh
  have hh := (card_le_card hcover).trans (card_union_le _ _)
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hh
  exact hh.trans (Nat.add_le_add_left hupper (N / 2 ^ J))

theorem density_transfer (N Y J : ℕ) (hN : 0 < N) (hY : 2 ≤ Y) (δ : ℝ)
    (hfull : δ * (N : ℝ) ≤ (smoothUpTo N Y).card)
    (hJ : 1 / (((2 : ℕ) ^ J : ℕ) : ℝ) ≤ δ / 2) :
    δ / (2 * (J + 1)) * (N : ℝ) ≤ (dyadicSmooth N Y).card := by
  have hp : (0 : ℝ) < (((2 : ℕ) ^ J : ℕ) : ℝ) := by positivity
  have hfloor : ((N / 2 ^ J : ℕ) : ℝ) ≤ (N : ℝ) / (((2 : ℕ) ^ J : ℕ) : ℝ) := by
    apply (le_div_iff₀ hp).mpr
    exact_mod_cast Nat.div_mul_le_self N (2 ^ J)
  have hsmall := hfloor.trans (show (N : ℝ) / (((2 : ℕ) ^ J : ℕ) : ℝ) ≤ δ / 2 * N by
    have hh := mul_le_mul_of_nonneg_right hJ (Nat.cast_nonneg (α := ℝ) N)
    calc
      _ = (1 / (((2 : ℕ) ^ J : ℕ) : ℝ)) * N := by ring
      _ ≤ _ := hh)
  have hc : ((smoothUpTo N Y).card : ℝ) ≤ ((N / 2 ^ J : ℕ) : ℝ) +
      ((J + 1 : ℕ) : ℝ) * (dyadicSmooth N Y).card := by exact_mod_cast finite_transfer N Y J hN hY
  push_cast at hc
  have hmain : δ / 2 * N ≤ ((J : ℝ) + 1) * (dyadicSmooth N Y).card := by
    nlinarith only [hfull, hsmall, hc]
  have hid : δ / (2 * (J + 1)) * (N : ℝ) = (δ / 2 * N) / ((J : ℝ) + 1) := by field_simp
  rw [hid]
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (J : ℝ) + 1)).mpr (by simpa only [mul_comm] using hmain)

end PaperP1.OrdinarySmoothDyadicDensity
