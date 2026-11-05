module

public import PaperP1.Arithmetic.OrdinarySmoothCensus
public import PaperP1.Arithmetic.OldValuePrimeBudget

/-! # Logarithmically weighted ordinary smooth-prime incidence

The weight log(p) pays for each prime divisor of a smooth integer at most log(n).
This gives an exact finite recursive lower-bound mechanism, without an assumed
smooth-number asymptotic or an uncontrolled factorization multiplicity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothPrimeIncidence

open Finset OrdinarySmoothCensus OddPrimePivot DefectCounting

def multiples (X Y p : ℕ) : Finset ℕ := (smoothUpTo X Y).filter fun n ↦ p ∣ n

theorem multiples_image {X Y p : ℕ} (hp : p.Prime) (hpy : p ≤ Y) :
    (smoothUpTo (X / p) Y).image (fun m ↦ p * m) = multiples X Y p := by
  ext n
  constructor
  · intro hn
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    obtain ⟨hm1, hmx, hmy⟩ := mem_smoothUpTo.mp hm
    have hmx' := (Nat.le_div_iff_mul_le hp.pos).mp hmx
    refine mem_filter.mpr ⟨mem_smoothUpTo.mpr ⟨by nlinarith only [hp.one_lt, hm1],
      by nlinarith only [hmx'], ?_⟩, dvd_mul_right p m⟩
    rw [largestPrimeFactor_mul hp.ne_zero (by omega), largestPrimeFactor_prime hp]
    exact max_le hpy hmy
  · intro hn
    obtain ⟨hs, hd⟩ := mem_filter.mp hn
    obtain ⟨hn1, hnx, hny⟩ := mem_smoothUpTo.mp hs
    apply mem_image.mpr
    refine ⟨n / p, mem_smoothUpTo.mpr ⟨?_, Nat.div_le_div_right hnx, ?_⟩,
      Nat.mul_div_cancel' hd⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
    · exact (largestPrimeFactor_of_dvd (Nat.div_dvd_of_dvd hd) (by omega)).trans hny

theorem multiples_card {X Y p : ℕ} (hp : p.Prime) (hpy : p ≤ Y) :
    (multiples X Y p).card = (smoothUpTo (X / p) Y).card := by
  rw [← multiples_image hp hpy, card_image_of_injective]
  exact fun a b h ↦ Nat.eq_of_mul_eq_mul_left hp.pos h

theorem primeDivisors_filter {n Y : ℕ} (hn : 0 < n) (hny : largestPrimeFactor n ≤ Y) :
    (smallPrimesUpTo Y).filter (fun p ↦ p ∣ n) = n.primeFactors := by
  ext p
  constructor
  · intro hp
    obtain ⟨hs, hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_smallPrimesUpTo.mp hs).1, hd, by omega⟩
  · intro hp
    refine mem_filter.mpr ⟨mem_smallPrimesUpTo.mpr ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩,
      Nat.dvd_of_mem_primeFactors hp⟩
    exact (Finset.le_sup (f := id) hp).trans ((le_max_right _ _).trans hny)

theorem weighted_identity (X Y : ℕ) :
    (∑ p ∈ smallPrimesUpTo Y, Real.log p * ((smoothUpTo (X / p) Y).card : ℝ)) =
      ∑ n ∈ smoothUpTo X Y, ∑ p ∈ n.primeFactors, Real.log p := by
  calc
    _ = ∑ p ∈ smallPrimesUpTo Y, ∑ n ∈ smoothUpTo X Y, if p ∣ n then Real.log p else 0 := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hpp, hpy⟩ := mem_smallPrimesUpTo.mp hp
      rw [← multiples_card hpp hpy, ← sum_filter]
      simp only [multiples, sum_const, nsmul_eq_mul, mul_comm]
    _ = ∑ n ∈ smoothUpTo X Y, ∑ p ∈ smallPrimesUpTo Y, if p ∣ n then Real.log p else 0 :=
      sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      obtain ⟨hn1, _, hny⟩ := mem_smoothUpTo.mp hn
      rw [← sum_filter, primeDivisors_filter (by omega : 0 < n) hny]

theorem weighted_recursion (X Y : ℕ) :
    (∑ p ∈ smallPrimesUpTo Y, Real.log p * ((smoothUpTo (X / p) Y).card : ℝ)) ≤
      Real.log X * (smoothUpTo X Y).card := by
  rw [weighted_identity]
  calc
    _ ≤ ∑ n ∈ smoothUpTo X Y, Real.log n := by
      apply sum_le_sum
      intro n hn
      exact OldValuePrimeBudget.primeFactors_log_sum_le (by have := (mem_smoothUpTo.mp hn).1; omega)
    _ ≤ ∑ _n ∈ smoothUpTo X Y, Real.log X := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn1, hnx, _⟩ := mem_smoothUpTo.mp hn
      exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnx)
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_comm]

theorem weighted_subset (X Y : ℕ) (T : Finset ℕ) (hT : T ⊆ smallPrimesUpTo Y) :
    (∑ p ∈ T, Real.log p * ((smoothUpTo (X / p) Y).card : ℝ)) ≤
      Real.log X * (smoothUpTo X Y).card := by
  exact (sum_le_sum_of_subset_of_nonneg hT (by
    intro p hp _
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.one_lt.le))
      (Nat.cast_nonneg _))).trans (weighted_recursion X Y)

theorem lower_transfer (X Y : ℕ) (T : Finset ℕ) (hT : T ⊆ smallPrimesUpTo Y) (a : ℝ)
    (hcount : ∀ p ∈ T, a * (X : ℝ) / (2 * p) ≤ (smoothUpTo (X / p) Y).card) :
    a * (X : ℝ) / 2 * (∑ p ∈ T, Real.log p / p) ≤
      Real.log X * (smoothUpTo X Y).card := by
  calc
    _ = ∑ p ∈ T, Real.log p * (a * (X : ℝ) / (2 * p)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ T, Real.log p * ((smoothUpTo (X / p) Y).card : ℝ) := by
      apply sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hcount p hp)
        (Real.log_nonneg (by exact_mod_cast (mem_smallPrimesUpTo.mp (hT hp)).1.one_lt.le))
    _ ≤ _ := weighted_subset X Y T hT

theorem count_lower_from_band (X Y : ℕ) (hX : 2 ≤ X) (T : Finset ℕ)
    (hT : T ⊆ smallPrimesUpTo Y) (a b : ℝ) (ha : 0 ≤ a)
    (hband : b ≤ ∑ p ∈ T, Real.log p / p)
    (hcount : ∀ p ∈ T, a * (X : ℝ) / (2 * p) ≤ (smoothUpTo (X / p) Y).card) :
    a * (X : ℝ) * b / (2 * Real.log X) ≤ (smoothUpTo X Y).card := by
  have hlog : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hh := (mul_le_mul_of_nonneg_left hband (show 0 ≤ a * (X : ℝ) / 2 by positivity)).trans
    (lower_transfer X Y T hT a hcount)
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log X)).mpr
  nlinarith only [hh]

end PaperP1.SmoothPrimeIncidence
