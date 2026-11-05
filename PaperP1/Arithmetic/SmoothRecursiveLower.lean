module

public import PaperP1.Arithmetic.SmoothPrimeIncidence

/-! # A finite smooth-density induction with a supplied prime band

A logarithmically weighted prime band lowers the remaining height by a factor R.
Iteration pays exactly one density factor per step, with every floor loss explicit.
The prime-band premises here are finite and remain explicit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothRecursiveLower

open Finset OrdinarySmoothCensus SmoothPrimeIncidence OddPrimePivot DefectCounting ReciprocalOddPivots

theorem smooth_below {X Y : ℕ} (hXY : X ≤ Y) : smoothUpTo X Y = Icc 1 X := by
  apply filter_eq_self.mpr
  intro n hn
  obtain ⟨hn1, hnx⟩ := mem_Icc.mp hn
  apply max_le (hn1.trans (hnx.trans hXY))
  apply Finset.sup_le
  intro p hp
  exact (Nat.le_of_mem_primeFactors hp).trans (hnx.trans hXY)

theorem smooth_below_card {X Y : ℕ} (hXY : X ≤ Y) : (smoothUpTo X Y).card = X := by
  rw [smooth_below hXY]
  simp

theorem floor_quotient_half {X p : ℕ} (hp : 0 < p) (hpx : p ≤ X) :
    (X : ℝ) / (2 * p) ≤ ((X / p : ℕ) : ℝ) := by
  have hq : 1 ≤ X / p := Nat.div_pos hpx hp
  have hr := Nat.mod_lt X hp
  have he := Nat.mod_add_div X p
  have hh : X ≤ 2 * p * (X / p) := by nlinarith only [hq, hr, he]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * p)).mpr
  exact_mod_cast (show X ≤ (X / p) * (2 * p) by nlinarith only [hh])

theorem geometric_density_lower (M Y : ℕ) (hY : 2 ≤ Y) (R r : ℝ)
    (hR : 0 < R) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (T : Finset ℕ)
    (hT : T ⊆ smallPrimesUpTo Y) (hscale : ∀ p ∈ T, R ≤ (p : ℝ))
    (hband : 2 * r * Real.log M ≤ ∑ p ∈ T, Real.log p / p) :
    ∀ k : ℕ, ∀ X : ℕ, 1 ≤ X → X ≤ M → (X : ℝ) ≤ (Y : ℝ) * R ^ k →
      (X : ℝ) * r ^ k ≤ (smoothUpTo X Y).card := by
  intro k
  induction k with
  | zero =>
    intro X _ _ hcap
    simp only [pow_zero, mul_one] at hcap ⊢
    have hxy : X ≤ Y := by exact_mod_cast hcap
    rw [smooth_below_card hxy]
  | succ k ih =>
    intro X hX hXM hcap
    by_cases hxy : X ≤ Y
    · rw [smooth_below_card hxy]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1 : r ^ (k + 1) ≤ 1) (Nat.cast_nonneg X)
    · have hxY : Y < X := by omega
      have hlogM : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
      have hcounts (p : ℕ) (hp : p ∈ T) :
          r ^ k * (X : ℝ) / (2 * p) ≤ (smoothUpTo (X / p) Y).card := by
        obtain ⟨hpp, hpy⟩ := mem_smallPrimesUpTo.mp (hT hp)
        have hpx : p ≤ X := by omega
        have hqpos : 1 ≤ X / p := Nat.div_pos hpx hpp.pos
        have hqM : X / p ≤ M := (Nat.div_le_self X p).trans hXM
        have hqr : ((X / p : ℕ) : ℝ) * R ≤ X := by
          calc
            _ ≤ ((X / p : ℕ) : ℝ) * p :=
              mul_le_mul_of_nonneg_left (hscale p hp) (Nat.cast_nonneg _)
            _ ≤ _ := by exact_mod_cast Nat.div_mul_le_self X p
        have hqcap : ((X / p : ℕ) : ℝ) ≤ (Y : ℝ) * R ^ k := by
          apply (mul_le_mul_iff_left₀ hR).mp
          exact hqr.trans (by simpa only [pow_succ, mul_assoc] using hcap)
        calc
          _ = r ^ k * ((X : ℝ) / (2 * p)) := by ring
          _ ≤ r ^ k * ((X / p : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (floor_quotient_half hpp.pos hpx) (pow_nonneg hr0 _)
          _ = ((X / p : ℕ) : ℝ) * r ^ k := by ring
          _ ≤ _ := ih (X / p) hqpos hqM hqcap
      have hh := (mul_le_mul_of_nonneg_left hband
        (show 0 ≤ r ^ k * (X : ℝ) / 2 by positivity)).trans
        (lower_transfer X Y T hT (r ^ k) hcounts)
      have hlogXM : Real.log X ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast hXM)
      have hh' := hh.trans (mul_le_mul_of_nonneg_right hlogXM
        (Nat.cast_nonneg (α := ℝ) (smoothUpTo X Y).card))
      apply (mul_le_mul_iff_left₀ hlogM).mp
      calc
        _ = (r ^ k * (X : ℝ) / 2) * (2 * r * Real.log M) := by rw [pow_succ]; ring
        _ ≤ _ := hh'
        _ = _ := by ring

theorem ordinary_reciprocal_lower (X Y : ℕ) :
    ((smoothUpTo X Y).card : ℝ) / Y ≤ primeSum X := by
  calc
    _ = ∑ _n ∈ smoothUpTo X Y, 1 / (Y : ℝ) := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ n ∈ smoothUpTo X Y, 1 / (largestPrimeFactor n : ℝ) := by
      apply sum_le_sum
      intro n hn
      exact one_div_le_one_div_of_le (by exact_mod_cast largestPrimeFactor_pos n)
        (by exact_mod_cast (mem_smoothUpTo.mp hn).2.2)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)

theorem geometric_reciprocal_lower (M Y : ℕ) (hY : 2 ≤ Y) (R r : ℝ)
    (hR : 0 < R) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (T : Finset ℕ)
    (hT : T ⊆ smallPrimesUpTo Y) (hscale : ∀ p ∈ T, R ≤ (p : ℝ))
    (hband : 2 * r * Real.log M ≤ ∑ p ∈ T, Real.log p / p)
    (k X : ℕ) (hX : 1 ≤ X) (hXM : X ≤ M) (hcap : (X : ℝ) ≤ (Y : ℝ) * R ^ k) :
    (X : ℝ) * r ^ k / Y ≤ primeSum X := by
  exact (div_le_div_of_nonneg_right
    (geometric_density_lower M Y hY R r hR hr0 hr1 T hT hscale hband k X hX hXM hcap)
    (Nat.cast_nonneg Y)).trans (ordinary_reciprocal_lower X Y)

end PaperP1.SmoothRecursiveLower
