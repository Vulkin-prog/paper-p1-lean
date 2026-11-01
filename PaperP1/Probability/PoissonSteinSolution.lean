module

public import PaperP1.Probability.PoissonPartialSums

/-! # A closed Poisson Stein solution and both unit Stein factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonSteinSolution

open Finset PaperP1.PoissonSequence PaperP1.PoissonPartialSums

def mean (μ : ℝ) (h : ℕ → ℝ) : ℝ := ∑' i, mass μ i * h i

def cumulative (μ : ℝ) (h : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range (k + 1), mass μ i * h i

def remainder (μ : ℝ) (h : ℕ → ℝ) (k : ℕ) : ℝ := mean μ h - cumulative μ h k

def successorSolution (μ : ℝ) (h : ℕ → ℝ) (k : ℕ) : ℝ :=
  (cumulative μ h k - cdf μ k * mean μ h) / (μ * mass μ k)

def solution (μ : ℝ) (h : ℕ → ℝ) (k : ℕ) : ℝ := successorSolution μ h (k - 1)

theorem summable_test {μ : ℝ} (hμ : 0 ≤ μ) {h : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) :
    Summable (fun i ↦ mass μ i * h i) :=
  (hasSum_mass μ hμ).summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (mass_nonneg hμ i) (hh i).1)
    (fun i ↦ mul_le_of_le_one_right (mass_nonneg hμ i) (hh i).2)

theorem cumulative_succ (μ : ℝ) (h : ℕ → ℝ) (k : ℕ) :
    cumulative μ h (k + 1) = cumulative μ h k + mass μ (k + 1) * h (k + 1) :=
  sum_range_succ _ _

theorem cumulative_bounds {μ : ℝ} (hμ : 0 ≤ μ) {h : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    0 ≤ cumulative μ h k ∧ cumulative μ h k ≤ cdf μ k := by
  constructor
  · exact sum_nonneg (fun i _ ↦ mul_nonneg (mass_nonneg hμ i) (hh i).1)
  · exact sum_le_sum (fun i _ ↦ mul_le_of_le_one_right (mass_nonneg hμ i) (hh i).2)

theorem remainder_eq_tail {μ : ℝ} (hμ : 0 ≤ μ) {h : ℕ → ℝ}
    (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    remainder μ h k = ∑' i : ℕ, mass μ (i + (k + 1)) * h (i + (k + 1)) := by
  have hsum := (summable_test hμ hh).sum_add_tsum_nat_add (k + 1)
  change cumulative μ h k + _ = mean μ h at hsum
  exact (sub_eq_iff_eq_add).mpr (by linarith)

theorem remainder_bounds {μ : ℝ} (hμ : 0 ≤ μ) {h : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    0 ≤ remainder μ h k ∧ remainder μ h k ≤ tail μ k := by
  rw [remainder_eq_tail hμ hh k]
  constructor
  · exact tsum_nonneg (fun i ↦ mul_nonneg (mass_nonneg hμ _) (hh _).1)
  · have ht := (summable_nat_add_iff (k + 1)).mpr (summable_test hμ hh)
    exact ht.tsum_le_tsum (fun i ↦ mul_le_of_le_one_right (mass_nonneg hμ _) (hh _).2)
      (tail_summable hμ k)

theorem successor_factorization {μ : ℝ} (hμ : 0 < μ) (h : ℕ → ℝ) (k : ℕ) :
    successorSolution μ h k = upperFactor μ k * cumulative μ h k - lowerFactor μ k * remainder μ h k := by
  have htail : tail μ k = 1 - cdf μ k := by linarith [prefix_add_tail hμ.le k]
  unfold successorSolution upperFactor lowerFactor remainder
  rw [htail]
  ring

theorem factor_identity (μ : ℝ) (k : ℕ) : upperFactor μ k * cdf μ k = lowerFactor μ k * tail μ k := by
  unfold upperFactor lowerFactor
  ring

theorem successor_abs_le_one {μ : ℝ} (hμ : 0 < μ) {h : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    |successorSolution μ h k| ≤ 1 := by
  obtain ⟨hP0, hP1⟩ := cumulative_bounds hμ.le hh k
  obtain ⟨hT0, hT1⟩ := remainder_bounds hμ.le hh k
  have hu := upperFactor_nonneg hμ k
  have hl := lowerFactor_nonneg hμ k
  have hu1 := mul_le_mul_of_nonneg_left hP1 hu
  have hl1 := mul_le_mul_of_nonneg_left hT1 hl
  have hu0 := mul_nonneg hu hP0
  have hl0 := mul_nonneg hl hT0
  have hbound : upperFactor μ k * cdf μ k ≤ 1 := by
    unfold upperFactor
    rw [div_mul_eq_mul_div]
    apply (div_le_one (mul_pos hμ (mass_pos μ hμ k))).mpr
    simpa only [mul_comm] using prefix_mul_tail_bound hμ.le k
  have hid := factor_identity μ k
  rw [successor_factorization hμ h, abs_le]
  constructor <;> nlinarith

theorem adjacent_coefficients_sum {μ : ℝ} (hμ : 0 ≤ μ) (k : ℕ) :
    (upperFactor μ (k + 1) - upperFactor μ k) * cdf μ k -
      (lowerFactor μ (k + 1) - lowerFactor μ k) * tail μ (k + 1) +
      (upperFactor μ (k + 1) + lowerFactor μ k) * mass μ (k + 1) = 0 := by
  have h0 := factor_identity μ k
  have h1 := factor_identity μ (k + 1)
  rw [prefix_succ] at h1
  rw [tail_eq_mass_add hμ k] at h0
  nlinarith

theorem successor_difference {μ : ℝ} (hμ : 0 < μ) (h : ℕ → ℝ) (k : ℕ) :
    successorSolution μ h (k + 1) - successorSolution μ h k =
      (upperFactor μ (k + 1) - upperFactor μ k) * cumulative μ h k +
      ((upperFactor μ (k + 1) + lowerFactor μ k) * mass μ (k + 1)) * h (k + 1) -
      (lowerFactor μ (k + 1) - lowerFactor μ k) * remainder μ h (k + 1) := by
  rw [successor_factorization hμ, successor_factorization hμ]
  have hcum := cumulative_succ μ h k
  have hrem : remainder μ h k = remainder μ h (k + 1) + mass μ (k + 1) * h (k + 1) := by
    unfold remainder
    rw [hcum]
    ring
  rw [hcum, hrem]
  ring

theorem successor_difference_abs_le_one {μ : ℝ} (hμ : 0 < μ) {h : ℕ → ℝ}
    (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    |successorSolution μ h (k + 1) - successorSolution μ h k| ≤ 1 := by
  obtain ⟨hP0, hP1⟩ := cumulative_bounds hμ.le hh k
  obtain ⟨hT0, hT1⟩ := remainder_bounds hμ.le hh (k + 1)
  have hu : upperFactor μ (k + 1) - upperFactor μ k ≤ 0 := sub_nonpos.mpr (upperFactor_antitone hμ k)
  have hl : 0 ≤ lowerFactor μ (k + 1) - lowerFactor μ k := sub_nonneg.mpr (lowerFactor_mono hμ k)
  have hupper0 := mul_nonpos_of_nonpos_of_nonneg hu hP0
  have hupper1 := mul_nonneg hl hT0
  have hlower0 := mul_le_mul_of_nonpos_left hP1 hu
  have hlower1 := mul_le_mul_of_nonneg_left hT1 hl
  have hc0 : 0 ≤ (upperFactor μ (k + 1) + lowerFactor μ k) * mass μ (k + 1) :=
    mul_nonneg (add_nonneg (upperFactor_nonneg hμ _) (lowerFactor_nonneg hμ _)) (mass_nonneg hμ.le _)
  have hc1 := adjacent_factor_bound hμ k
  have hmid0 := mul_nonneg hc0 (hh (k + 1)).1
  have hmid1 := mul_le_of_le_one_right hc0 (hh (k + 1)).2
  have hsum := adjacent_coefficients_sum hμ.le k
  rw [successor_difference hμ, abs_le]
  constructor <;> nlinarith

theorem solution_abs_le_one {μ : ℝ} (hμ : 0 < μ) {h : ℕ → ℝ} (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    |solution μ h k| ≤ 1 := successor_abs_le_one hμ hh (k - 1)

theorem solution_difference_abs_le_one {μ : ℝ} (hμ : 0 < μ) {h : ℕ → ℝ}
    (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) (k : ℕ) :
    |solution μ h (k + 1) - solution μ h k| ≤ 1 := by
  cases k with
  | zero => simp [solution]
  | succ k => simpa only [solution, Nat.add_sub_cancel] using successor_difference_abs_le_one hμ hh k

theorem successor_normalization {μ : ℝ} (hμ : 0 < μ) (h : ℕ → ℝ) (k : ℕ) :
    μ * mass μ k * successorSolution μ h k = cumulative μ h k - cdf μ k * mean μ h := by
  unfold successorSolution
  exact mul_div_cancel₀ _ (mul_pos hμ (mass_pos μ hμ k)).ne'

theorem stein_equation {μ : ℝ} (hμ : 0 < μ) (h : ℕ → ℝ) (k : ℕ) :
    μ * solution μ h (k + 1) - (k : ℝ) * solution μ h k = h k - mean μ h := by
  cases k with
  | zero =>
    have hn := successor_normalization hμ h 0
    norm_num [cumulative, cdf] at hn
    simp only [solution, Nat.add_sub_cancel, Nat.zero_sub, Nat.cast_zero, zero_mul, sub_zero]
    have hp := mass_pos μ hμ 0
    nlinarith
  | succ k =>
    have h0 := successor_normalization hμ h k
    have h1 := successor_normalization hμ h (k + 1)
    rw [cumulative_succ, prefix_succ] at h1
    have hrec := mass_succ_mul μ k
    push_cast at hrec ⊢
    have hprod := congrArg (fun z : ℝ ↦ z * successorSolution μ h k) hrec
    change μ * successorSolution μ h (k + 1) - (k + 1 : ℝ) * successorSolution μ h k = h (k + 1) - mean μ h
    apply (mul_left_cancel₀ (mass_pos μ hμ (k + 1)).ne')
    nlinarith

/-- The standard two unit bounds are closed proofs, not external Stein inputs. -/
theorem unit_stein_factors (μ : ℝ) (hμ : 0 < μ) (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i ∧ h i ≤ 1) :
    ∃ f : ℕ → ℝ, (∀ k, μ * f (k + 1) - (k : ℝ) * f k = h k - mean μ h) ∧
      (∀ k, |f k| ≤ 1) ∧ (∀ k, |f (k + 1) - f k| ≤ 1) :=
  ⟨solution μ h, stein_equation hμ h, solution_abs_le_one hμ hh, solution_difference_abs_le_one hμ hh⟩

end PaperP1.PoissonSteinSolution
