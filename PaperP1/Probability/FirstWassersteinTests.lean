module

public import PaperP1.Probability.FirstWasserstein

/-! # Marginal test identities and lower bounds for first Wasserstein transport

Absolutely integrable marginal tests are absolutely integrable under every
transport plan. Every one-Lipschitz test gives a lower bound for the actual
transport infimum. On the naturals this also implies TV <= W1.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstWassersteinTests

open MeasureTheory PaperP1.AtomicProbability PaperP1.FirstWasserstein

theorem matrix_test_summable (m : ℕ × ℕ → ℝ) (hm : ∀ p, 0 ≤ m p)
    (a : ℕ → ℝ) (hrow : ∀ i, HasSum (fun j ↦ m (i, j)) (a i))
    (f : ℕ → ℝ) (hf : Summable (fun i ↦ a i * |f i|)) :
    Summable (fun p ↦ m p * f p.1) := by
  have hr (i : ℕ) := (hrow i).mul_right |f i|
  have he (i : ℕ) : (∑' j, m (i, j) * |f i|) = a i * |f i| := (hr i).tsum_eq
  have hs : Summable (fun p : ℕ × ℕ ↦ m p * |f p.1|) :=
    (summable_prod_of_nonneg (fun p ↦ mul_nonneg (hm p) (abs_nonneg _))).mpr
      ⟨fun i ↦ (hr i).summable, by simpa only [he] using hf⟩
  apply hs.of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm p)]

theorem row_test_summable {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) (f : ℕ → ℝ)
    (hf : Summable (fun i ↦ realMass P i * |f i|)) :
    Summable (fun p ↦ π.mass p * f p.1) :=
  matrix_test_summable π.mass π.nonneg _ π.row f hf

theorem column_test_summable {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) (f : ℕ → ℝ)
    (hf : Summable (fun j ↦ realMass Q j * |f j|)) :
    Summable (fun p ↦ π.mass p * f p.2) := by
  have hs := matrix_test_summable (fun p ↦ π.mass (p.2, p.1))
    (fun p ↦ π.nonneg (p.2, p.1)) _ π.column f hf
  exact hs.prod_symm

theorem row_test_sum {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) (f : ℕ → ℝ)
    (hf : Summable (fun i ↦ realMass P i * |f i|)) :
    (∑' p, π.mass p * f p.1) = AtomicTests.expectation P f := by
  rw [(row_test_summable π f hf).tsum_prod]
  exact tsum_congr (fun i ↦ ((π.row i).mul_right (f i)).tsum_eq)

theorem column_test_sum {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) (f : ℕ → ℝ)
    (hf : Summable (fun j ↦ realMass Q j * |f j|)) :
    (∑' p, π.mass p * f p.2) = AtomicTests.expectation Q f := by
  have hs := column_test_summable π f hf
  rw [hs.tsum_prod, ← hs.tsum_comm]
  exact tsum_congr (fun j ↦ ((π.column j).mul_right (f j)).tsum_eq)

theorem test_cost_bound {P Q : ProbabilityMeasure ℕ} (π : Plan P Q) (f : ℕ → ℝ)
    (hP : Summable (fun i ↦ realMass P i * |f i|))
    (hQ : Summable (fun j ↦ realMass Q j * |f j|))
    (hf : ∀ i j : ℕ, |f i - f j| ≤ |(i : ℝ) - (j : ℝ)|) :
    |AtomicTests.expectation P f - AtomicTests.expectation Q f| ≤ cost π := by
  have hsP := row_test_summable π f hP
  have hsQ := column_test_summable π f hQ
  have hd := hsP.sub hsQ
  have he : (∑' p, (π.mass p * f p.1 - π.mass p * f p.2)) =
      AtomicTests.expectation P f - AtomicTests.expectation Q f := by
    rw [hsP.tsum_sub hsQ, row_test_sum π f hP, column_test_sum π f hQ]
  rw [← he]
  calc
    _ ≤ ∑' p, |π.mass p * f p.1 - π.mass p * f p.2| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hd.norm
    _ ≤ cost π := hd.abs.tsum_le_tsum (fun p ↦ by
      rw [← mul_sub, abs_mul, abs_of_nonneg (π.nonneg p)]
      exact mul_le_mul_of_nonneg_left (hf p.1 p.2) (π.nonneg p)) π.cost_summable

theorem test_distance_bound (P Q : ProbabilityMeasure ℕ) (hPQ : Nonempty (Plan P Q))
    (f : ℕ → ℝ) (hP : Summable (fun i ↦ realMass P i * |f i|))
    (hQ : Summable (fun j ↦ realMass Q j * |f j|))
    (hf : ∀ i j : ℕ, |f i - f j| ≤ |(i : ℝ) - (j : ℝ)|) :
    |AtomicTests.expectation P f - AtomicTests.expectation Q f| ≤ distance P Q hPQ := by
  obtain ⟨π⟩ := hPQ
  apply le_csInf (show (Set.range (fun π : Plan P Q ↦ cost π)).Nonempty from
    ⟨cost π, Set.mem_range_self π⟩)
  rintro r ⟨ρ, rfl⟩
  exact test_cost_bound ρ f hP hQ hf

theorem unit_test_lipschitz (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (i j : ℕ) :
    |f i - f j| ≤ |(i : ℝ) - (j : ℝ)| := by
  by_cases hij : i = j
  · simp only [hij, sub_self, abs_zero, le_refl]
  · have htest : |f i - f j| ≤ 1 := abs_le.mpr ⟨by linarith only [(hf i).1, (hf j).2],
      by linarith only [(hf i).2, (hf j).1]⟩
    apply htest.trans
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hreal : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith only [hreal])]
      linarith only [hreal]
    · have hreal : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
      rw [abs_of_nonneg (by linarith only [hreal])]
      linarith only [hreal]

theorem totalVariation_le_distance (P Q : ProbabilityMeasure ℕ) (hPQ : Nonempty (Plan P Q)) :
    totalVariation P Q ≤ distance P Q hPQ := by
  let f := AtomicTests.attainingTest P Q
  have hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1 := AtomicTests.attainingTest_bounds P Q
  have htest (R : ProbabilityMeasure ℕ) : Summable (fun i ↦ realMass R i * |f i|) :=
    AtomicTests.summable_mul_unit (hasSum_realMass R).summable (fun i ↦ by
      rw [abs_abs, abs_of_nonneg (hf i).1]
      exact (hf i).2)
  have hh := test_distance_bound P Q hPQ f (htest P) (htest Q) (unit_test_lipschitz f hf)
  rw [AtomicTests.attainingTest_difference, abs_of_nonneg (totalVariation_nonneg P Q)] at hh
  exact hh

end PaperP1.FirstWassersteinTests
