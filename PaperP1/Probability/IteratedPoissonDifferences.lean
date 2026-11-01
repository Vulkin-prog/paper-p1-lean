module

public import PaperP1.Probability.FiniteShiftAction
public import PaperP1.Probability.PoissonFactorialMoments

/-! # Summability, exact factorial moments and coarse norms of every Poisson difference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IteratedPoissonDifferences

open Finset PaperP1.PoissonSequence PaperP1.PoissonFactorialMoments PaperP1.FiniteShiftAction

def l1 (a : ℕ → ℝ) : ℝ := ∑' k : ℕ, |a k|

theorem summable_difference (r : ℕ) (a : ℕ → ℝ) (ha : Summable a) : Summable (difference r a) := by
  induction r with
  | zero => simpa only [difference_zero] using ha
  | succ r ih =>
    rw [difference_succ]
    exact (hasSum_shift ih.hasSum).summable.sub ih

theorem l1_shift (a : ℕ → ℝ) (ha : Summable a) : l1 (shift a) = l1 a := by
  have hid : (fun k : ℕ ↦ |shift a k|) = shift (fun k ↦ |a k|) := by
    funext k
    cases k <;> simp
  unfold l1
  rw [hid]
  exact (hasSum_shift ha.abs.hasSum).tsum_eq

theorem l1_nonneg (a : ℕ → ℝ) : 0 ≤ l1 a := tsum_nonneg (fun _ ↦ abs_nonneg _)

theorem l1_sub_le (a b : ℕ → ℝ) (ha : Summable a) (hb : Summable b) :
    l1 (a - b) ≤ l1 a + l1 b := by
  calc
    _ ≤ ∑' k : ℕ, (|a k| + |b k|) := (ha.sub hb).abs.tsum_le_tsum (fun k ↦ abs_sub (a k) (b k)) (ha.abs.add hb.abs)
    _ = _ := ha.abs.tsum_add hb.abs

theorem l1_difference_le (r : ℕ) (a : ℕ → ℝ) (ha : Summable a) :
    l1 (difference r a) ≤ (2 : ℝ) ^ r * l1 a := by
  induction r with
  | zero => simp only [difference_zero, pow_zero, one_mul, le_refl]
  | succ r ih =>
    have hs := summable_difference r a ha
    calc
      _ ≤ l1 (shift (difference r a)) + l1 (difference r a) := by
        rw [difference_succ]
        exact l1_sub_le _ _ (hasSum_shift hs.hasSum).summable hs
      _ = 2 * l1 (difference r a) := by rw [l1_shift _ hs]; ring
      _ ≤ 2 * ((2 : ℝ) ^ r * l1 a) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem l1_poisson (μ : ℝ) (hμ : 0 ≤ μ) : l1 (mass μ) = 1 := by
  unfold l1
  have habs : (fun k : ℕ ↦ |mass μ k|) = mass μ := by
    funext k
    apply abs_of_nonneg
    unfold mass
    positivity
  rw [habs]
  exact (hasSum_mass μ hμ).tsum_eq

theorem l1_poisson_difference_le (μ : ℝ) (hμ : 0 ≤ μ) (r : ℕ) :
    l1 (difference r (mass μ)) ≤ (2 : ℝ) ^ r := by
  simpa only [l1_poisson μ hμ, mul_one] using l1_difference_le r (mass μ) (hasSum_mass μ hμ).summable

theorem hasSum_difference_factorial (μ : ℝ) (hμ : 0 ≤ μ) (r j : ℕ) :
    HasSum (fun k : ℕ ↦ difference r (mass μ) k * (k.descFactorial j : ℝ))
      ((j.descFactorial r : ℝ) * μ ^ (j - r)) := by
  induction r generalizing j with
  | zero =>
    simpa only [difference_zero, Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.sub_zero] using
      hasSum_mass_factorial μ hμ j
  | succ r ih =>
    cases j with
    | zero =>
      have h := (hasSum_shift (ih 0)).sub (ih 0)
      simpa only [difference_succ, Pi.sub_apply, Nat.descFactorial_zero, Nat.cast_one, mul_one,
        sub_self, Nat.zero_descFactorial_succ, Nat.cast_zero, zero_mul] using h
    | succ j =>
      have hshift : HasSum (fun k : ℕ ↦ shift (difference r (mass μ)) k * (k.descFactorial (j + 1) : ℝ))
          ((↑((j + 1).descFactorial r) : ℝ) * μ ^ (j + 1 - r) +
            (j + 1 : ℝ) * ((j.descFactorial r : ℝ) * μ ^ (j - r))) := by
        apply hasSum_shift_weighted
        have h := (ih (j + 1)).add ((ih j).mul_left (j + 1 : ℝ))
        convert h using 1
        funext k
        rw [descFactorial_succ_add]
        push_cast
        ring
      have h := hshift.sub (ih (j + 1))
      convert h using 1
      · funext k
        simp only [difference_succ, Pi.sub_apply]
        ring
      · rw [Nat.succ_descFactorial_succ, Nat.succ_sub_succ_eq_sub, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring

theorem shiftBy_mass (μ : ℝ) (hμ : μ ≠ 0) (j k : ℕ) :
    shiftBy j (mass μ) k = mass μ k * (k.descFactorial j : ℝ) / μ ^ j := by
  by_cases hkj : j ≤ k
  · let n := k - j
    have hk : k = n + j := by dsimp [n]; omega
    rw [hk, shiftBy_at_add]
    apply (eq_div_iff (pow_ne_zero j hμ)).mpr
    rw [mul_comm (mass μ n) (μ ^ j)]
    exact (mass_add_mul_descFactorial μ n j).symm
  · have hk : k < j := by omega
    rw [shiftBy_of_lt j _ k hk, Nat.descFactorial_of_lt hk, Nat.cast_zero, mul_zero, zero_div]

end PaperP1.IteratedPoissonDifferences
