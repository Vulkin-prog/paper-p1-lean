module

public import PaperP1.Probability.JumpPoissonSeries
public import PaperP1.Probability.FinitePoissonCharlierConversion

/-! # Universal stability in the actual Poisson and quadratic parameters

The mean Lipschitz constant is independent of an upper mean bound. Signed
quadratic references permit arbitrary real second parameters throughout.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonParameterStability

open PaperP1.Probability PaperP1.CompletedLaw PaperP1.CompletedPoisson
  PaperP1.CompletedLawShift PaperP1.PoissonSequence

theorem norm_poisson_sub_one {μ : ℝ} (hμ : 0 ≤ μ) :
    ‖poisson μ - 1‖ ≤ 2 * (1 - Real.exp (-μ)) := by
  have he : Real.exp (-μ) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hμ)
  have hsum : HasSum (fun n : ℕ ↦ mass μ n • ofFinite (atom n)) (poisson μ) := by
    simpa only [one_mul, JumpPoissonSeries.jump_one] using JumpPoissonSeries.hasSum_jumpPoisson 1 μ
  have hspace := hsum.sub (hasSum_ite_eq (0 : ℕ) (1 : Space))
  have hreal := (hasSum_mass μ hμ).add (hasSum_ite_eq (0 : ℕ) (1 - 2 * Real.exp (-μ)))
  have hmajor : HasSum (fun n : ℕ ↦ mass μ n + if n = 0 then 1 - 2 * Real.exp (-μ) else 0)
      (2 * (1 - Real.exp (-μ))) := by convert hreal using 1; ring
  apply hspace.norm_le_of_bounded hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    have hid : mass μ 0 • ofFinite (atom 0) - (if (0 : ℕ) = 0 then (1 : Space) else 0) =
        (Real.exp (-μ) - 1) • (1 : Space) := by
      simp only [mass, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one,
        atom_zero, map_one, ite_true, sub_smul, one_smul]
    rw [hid, norm_smul, Real.norm_eq_abs, norm_one, mul_one,
      abs_of_nonpos (sub_nonpos.mpr he)]
    simp only [mass, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one, ite_true]
    linarith
  · simp only [hn, ite_false, sub_zero, add_zero]
    have hnorm := JumpPoissonSeries.norm_term 1 μ n
    simpa only [one_mul, abs_of_nonneg (PoissonPartialSums.mass_nonneg hμ n)] using hnorm.le

theorem norm_poisson_sub_one_linear {μ : ℝ} (hμ : 0 ≤ μ) : ‖poisson μ - 1‖ ≤ 2 * μ := by
  have he := Real.add_one_le_exp (-μ)
  exact (norm_poisson_sub_one hμ).trans (by linarith only [he])

theorem poisson_add (μ ν : ℝ) : poisson (μ + ν) = poisson μ * poisson ν := by
  simp only [poisson, add_smul, NormedSpace.exp_add]

theorem ordered_norm_difference {μ ν : ℝ} (hμ : 0 ≤ μ) (hμν : μ ≤ ν) :
    ‖poisson ν - poisson μ‖ ≤ 2 * (ν - μ) := by
  have hid : poisson ν - poisson μ = poisson μ * (poisson (ν - μ) - 1) := by
    rw [mul_sub, mul_one, ← poisson_add, add_sub_cancel]
  rw [hid]
  calc
    _ ≤ ‖poisson μ‖ * ‖poisson (ν - μ) - 1‖ := norm_mul_le _ _
    _ = ‖poisson (ν - μ) - 1‖ := by rw [JumpPoissonSeries.norm_poisson hμ, one_mul]
    _ ≤ _ := norm_poisson_sub_one_linear (sub_nonneg.mpr hμν)

theorem norm_difference {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) :
    ‖poisson μ - poisson ν‖ ≤ 2 * |μ - ν| := by
  rcases le_total μ ν with h | h
  · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered_norm_difference hμ h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered_norm_difference hν h

theorem norm_quadratic_coefficient_difference {μ : ℝ} (hμ : 0 ≤ μ) (α β : ℝ) :
    ‖quadratic μ α - quadratic μ β‖ ≤ 2 * |α - β| := by
  have hid : quadratic μ α - quadratic μ β = ((α - β) / 2) • (delta ^ 2 * poisson μ) := by
    unfold quadratic
    module
  have hprod : ‖delta ^ 2 * poisson μ‖ ≤ 4 := by
    exact (norm_mul_le _ _).trans (by simpa only [JumpPoissonSeries.norm_poisson hμ, mul_one] using
      FinitePoissonCharlierConversion.norm_delta_squared_le)
  rw [hid, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith only [mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ |α - β| / 2)]

theorem norm_quadratic_mean_difference {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (α : ℝ) :
    ‖quadratic μ α - quadratic ν α‖ ≤ 2 * (1 + 2 * |α|) * |μ - ν| := by
  have hid : quadratic μ α - quadratic ν α =
      (poisson μ - poisson ν) + (α / 2) • (delta ^ 2 * (poisson μ - poisson ν)) := by
    unfold quadratic
    simp only [mul_sub]
    module
  have hdelta := FinitePoissonCharlierConversion.norm_delta_squared_le
  have hmean := norm_difference hμ hν
  rw [hid]
  calc
    _ ≤ ‖poisson μ - poisson ν‖ + ‖(α / 2) • (delta ^ 2 * (poisson μ - poisson ν))‖ := norm_add_le _ _
    _ ≤ ‖poisson μ - poisson ν‖ + (|α| / 2) * (4 * ‖poisson μ - poisson ν‖) := by
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hdelta (norm_nonneg _))
    _ ≤ 2 * (1 + 2 * |α|) * |μ - ν| := by
      nlinarith only [hmean, mul_le_mul_of_nonneg_left hmean (abs_nonneg α)]

theorem norm_quadratic_difference {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (α β : ℝ) :
    ‖quadratic μ α - quadratic ν β‖ ≤
      2 * (1 + 2 * |α|) * |μ - ν| + 2 * |α - β| := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (quadratic ν α) _).trans
    (add_le_add (norm_quadratic_mean_difference hμ hν α)
      (norm_quadratic_coefficient_difference hν α β))

theorem actual_signed_difference {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (α β : ℝ) :
    (∑' k : ℕ, |(QuadraticPoisson.reference μ α - QuadraticPoisson.reference ν β) {k}|) ≤
      2 * (1 + 2 * |α|) * |μ - ν| + 2 * |α - β| := by
  have heq (k : ℕ) :
      (QuadraticPoisson.reference μ α - QuadraticPoisson.reference ν β) {k} =
        coeff k (quadratic μ α - quadratic ν β) := by
    rw [← quadratic_actual_signed_measure μ α, ← quadratic_actual_signed_measure ν β,
      _root_.sub_apply, toSignedMeasure_singleton, toSignedMeasure_singleton, map_sub]
  simp_rw [heq]
  exact (tsum_abs_coeff_le _).trans (norm_quadratic_difference hμ hν α β)

end PaperP1.PoissonParameterStability
