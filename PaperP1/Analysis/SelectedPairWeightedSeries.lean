module

public import PaperP1.Analysis.ExponentialPowerSum
public import PaperP1.Algebra.NonnegativePowerDifference
public import Mathlib.Data.Nat.Choose.Bounds

/-! # Uniform finite weighted comparison of selected pair moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedPairWeightedSeries

open Finset PaperP1.ExponentialPowerSum

def error (B : ℕ → ℝ) (μ α : ℝ) (m : ℕ) : ℝ :=
  ∑ r ∈ Icc 2 m, ((2 : ℝ) ^ (r - 1) / (r.factorial : ℝ)) *
    |B r - (r.choose 2 : ℝ) * μ ^ (r - 2) * α|

theorem kernel_change (ellMean μ A α M : ℝ) (hE : 0 ≤ ellMean) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (hEM : ellMean ≤ M) (hμM : μ ≤ M) (k : ℕ) :
    |ellMean ^ k * A - μ ^ k * α| ≤
      |ellMean - μ| * k * M ^ (k - 1) * A + M ^ k * |A - α| := by
  have hp := NonnegativePowerDifference.bound ellMean μ M hE hμ hEM hμM k
  calc
    _ = |(ellMean ^ k - μ ^ k) * A + μ ^ k * (A - α)| := by congr 1; ring
    _ ≤ |(ellMean ^ k - μ ^ k) * A| + |μ ^ k * (A - α)| := abs_add_le _ _
    _ = |ellMean ^ k - μ ^ k| * A + μ ^ k * |A - α| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg (pow_nonneg hμ _)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hp hA)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hμ hμM k) (abs_nonneg _))

theorem point_bound (B ellMean μ A α M δ : ℝ) (hE : 0 ≤ ellMean) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (hM : 1 ≤ M) (hEM : ellMean ≤ M) (hμM : μ ≤ M) (hδ : 0 ≤ δ) (r : ℕ)
    (hB : |B - (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A| ≤
      (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A * δ) :
    |B - (r.choose 2 : ℝ) * μ ^ (r - 2) * α| ≤
      (r : ℝ) ^ 2 * M ^ r * (A * δ + A * |ellMean - μ| * r + |A - α|) := by
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hkr : (r - 2 : ℕ) ≤ r := Nat.sub_le r 2
  have hkrR : ((r - 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast hkr
  have hpow : M ^ (r - 2) ≤ M ^ r := pow_le_pow_right₀ hM hkr
  have hpred : M ^ ((r - 2) - 1) ≤ M ^ r := pow_le_pow_right₀ hM (by omega)
  have hEpow : ellMean ^ (r - 2) ≤ M ^ r := (pow_le_pow_left₀ hE hEM _).trans hpow
  have hkernel := kernel_change ellMean μ A α M hE hμ hA hEM hμM (r - 2)
  have hfirst : ellMean ^ (r - 2) * A * δ ≤ M ^ r * (A * δ) := by
    have hh := mul_le_mul_of_nonneg_right hEpow (mul_nonneg hA hδ)
    simpa only [mul_assoc] using hh
  have hcross : |ellMean - μ| * (r - 2 : ℕ) * M ^ ((r - 2) - 1) * A ≤
      M ^ r * (A * |ellMean - μ| * r) := by
    have hsmall := mul_le_mul hkrR hpred (pow_nonneg hM0 _) (Nat.cast_nonneg r)
    have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hA (abs_nonneg (ellMean - μ)))
    convert hh using 1 <;> ring
  have hlast := mul_le_mul_of_nonneg_right hpow (abs_nonneg (A - α))
  have htri := abs_sub_le B ((r.choose 2 : ℝ) * ellMean ^ (r - 2) * A)
    ((r.choose 2 : ℝ) * μ ^ (r - 2) * α)
  rw [show (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A - (r.choose 2 : ℝ) * μ ^ (r - 2) * α =
    (r.choose 2 : ℝ) * (ellMean ^ (r - 2) * A - μ ^ (r - 2) * α) by ring,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg (r.choose 2) : (0 : ℝ) ≤ (r.choose 2 : ℝ))] at htri
  have hmiddle : |B - (r.choose 2 : ℝ) * μ ^ (r - 2) * α| ≤
      (r.choose 2 : ℝ) * (M ^ r * (A * δ + A * |ellMean - μ| * r + |A - α|)) := by
    have hk := mul_le_mul_of_nonneg_left hkernel (Nat.cast_nonneg (r.choose 2) : (0 : ℝ) ≤ _)
    have hsum : ellMean ^ (r - 2) * A * δ +
        |ellMean - μ| * (r - 2 : ℕ) * M ^ ((r - 2) - 1) * A + M ^ (r - 2) * |A - α| ≤
        M ^ r * (A * δ + A * |ellMean - μ| * r + |A - α|) := by
      have hh := add_le_add (add_le_add hfirst hcross) hlast
      convert hh using 1; ring
    have hscaled := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (r.choose 2) : (0 : ℝ) ≤ _)
    nlinarith only [htri, hB, hk, hscaled]
  have hchoose : (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow r 2
  exact hmiddle.trans ((mul_le_mul_of_nonneg_right hchoose (by positivity)).trans_eq (by ring))

theorem finite_bound (B : ℕ → ℝ) (ellMean μ A α M δ : ℝ) (m : ℕ)
    (hE : 0 ≤ ellMean) (hμ : 0 ≤ μ) (hA : 0 ≤ A) (hM : 1 ≤ M)
    (hEM : ellMean ≤ M) (hμM : μ ≤ M) (hδ : 0 ≤ δ)
    (hB : ∀ r ∈ Icc 2 m, |B r - (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A| ≤
      (r.choose 2 : ℝ) * ellMean ^ (r - 2) * A * δ) :
    error B μ α m ≤ 6 * Real.exp (Real.exp 1 * (2 * M)) *
      (A * δ + A * |ellMean - μ| + |A - α|) := by
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hpoint (r : ℕ) (hr : r ∈ Icc 2 m) :
      ((2 : ℝ) ^ (r - 1) / (r.factorial : ℝ)) * |B r - (r.choose 2 : ℝ) * μ ^ (r - 2) * α| ≤
      (A * δ + |A - α|) * term 2 (2 * M) r + (A * |ellMean - μ|) * term 3 (2 * M) r := by
    calc
      _ ≤ ((2 : ℝ) ^ r / (r.factorial : ℝ)) *
          ((r : ℝ) ^ 2 * M ^ r * (A * δ + A * |ellMean - μ| * r + |A - α|)) :=
        mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
          (Nat.sub_le r 1)) (Nat.cast_nonneg _))
          (point_bound (B r) ellMean μ A α M δ hE hμ hA hM hEM hμM hδ r (hB r hr))
          (abs_nonneg _) (by positivity)
      _ = _ := by unfold term; rw [mul_pow]; ring
  have h2 := Summable.sum_le_tsum (Icc 2 m) (fun _ _ ↦ term_nonneg 2 (2 * M) (by positivity) _)
    (summable_term 2 (2 * M) (by positivity))
  have h3 := Summable.sum_le_tsum (Icc 2 m) (fun _ _ ↦ term_nonneg 3 (2 * M) (by positivity) _)
    (summable_term 3 (2 * M) (by positivity))
  have ht2 := total_le 2 (2 * M) (by positivity)
  have ht3 := total_le 3 (2 * M) (by positivity)
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul] at ht2 ht3
  calc
    _ ≤ ∑ r ∈ Icc 2 m, ((A * δ + |A - α|) * term 2 (2 * M) r +
        (A * |ellMean - μ|) * term 3 (2 * M) r) := sum_le_sum hpoint
    _ = (A * δ + |A - α|) * (∑ r ∈ Icc 2 m, term 2 (2 * M) r) +
        (A * |ellMean - μ|) * ∑ r ∈ Icc 2 m, term 3 (2 * M) r := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ (A * δ + |A - α|) * (2 * Real.exp (Real.exp 1 * (2 * M))) +
        (A * |ellMean - μ|) * (6 * Real.exp (Real.exp 1 * (2 * M))) :=
      add_le_add (mul_le_mul_of_nonneg_left (h2.trans ht2) (by positivity))
        (mul_le_mul_of_nonneg_left (h3.trans ht3) (by positivity))
    _ ≤ _ := by
      have hh : 0 ≤ (A * δ + |A - α|) * Real.exp (Real.exp 1 * (2 * M)) := by positivity
      nlinarith only [hh]

end PaperP1.SelectedPairWeightedSeries
