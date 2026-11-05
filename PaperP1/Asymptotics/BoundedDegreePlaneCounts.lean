module

public import PaperP1.Arithmetic.FixedDegreeFieldPlaneCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Unconditional plane-count consequences on fixed finite degree intervals

Every upper degree bound is fixed before the height. No growing-degree BCN
estimate is inferred from the finite choice of constants.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedDegreePlaneCounts

open Polynomial Filter

theorem eventual_power_absorption (K a b : ℝ) (hab : a < b) :
    ∃ H₀ : ℝ, 2 < H₀ ∧ ∀ H ≥ H₀, K * H ^ a ≤ H ^ b := by
  have ht : Tendsto (fun H : ℝ ↦ K * H ^ (-(b - a))) atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul K
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max 3 T, by have hh := le_max_left (3 : ℝ) T; linarith, ?_⟩
  intro H hH
  have hHp : 0 < H := by have hh := le_max_left (3 : ℝ) T; linarith
  have he : (K * H ^ (-(b - a))) * H ^ b = K * H ^ a := by
    rw [mul_assoc, ← Real.rpow_add hHp]
    congr 2
    ring
  have hh := mul_le_mul_of_nonneg_right (hT H ((le_max_right _ _).trans hH)).le
    (Real.rpow_nonneg hHp.le b)
  simpa only [he, one_mul] using hh

theorem uniform_power_bound (d M : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      d ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ M →
      Irreducible P → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (d : ℝ) + ε) := by
  obtain ⟨K, hK, hcount⟩ := FixedDegreeFieldPlaneCount.bounded_degree_count M ε hε
  refine ⟨K, hK, ?_⟩
  intro F _hF _hchar P hD hM hP H hH
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hdegree : (d : ℝ) ≤ PlaneCurvePointCount.degree P := by exact_mod_cast hD
  have hfrac : 2 / (PlaneCurvePointCount.degree P : ℝ) ≤ 2 / (d : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hdp hdegree
  have hpow : H ^ (2 / (PlaneCurvePointCount.degree P : ℝ) + ε) ≤ H ^ (2 / (d : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact (hcount F P (by omega) hM hP H hH).trans (mul_le_mul_of_nonneg_left hpow hK)

theorem uniform_sublinear (M : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ H₀ : ℝ, 2 < H₀ ∧ ∀ H ≥ H₀, ∀ (F : Type*) [Field F] [CharZero F],
      ∀ P : F[X][X], 3 ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ M →
        Irreducible P → ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ η * H := by
  obtain ⟨K, _hK, hcount⟩ := uniform_power_bound 3 M (by omega) (1 / 6) (by norm_num)
  obtain ⟨H₀, hH₀, hsmall⟩ := eventual_power_absorption (K / η) (5 / 6) 1 (by norm_num)
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH F _hF _hchar P hD hM hP
  have hb := hcount F P hD hM hP H (hH₀.trans_le hH)
  norm_num only [show (2 : ℝ) / (3 : ℝ) + 1 / 6 = 5 / 6 by norm_num] at hb
  have hs := mul_le_mul_of_nonneg_left (hsmall H hH) hη.le
  have hcancel : η * (K / η) = K := by field_simp
  rw [← mul_assoc, hcancel, Real.rpow_one] at hs
  exact hb.trans hs

theorem uniform_subpower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ M : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      d ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ M →
      Irreducible P → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ K * H ^ ε := by
  obtain ⟨d, hd⟩ := exists_nat_gt (max 2 (4 / ε))
  have hdR : (2 : ℝ) < d := (le_max_left _ _).trans_lt hd
  have hdN : 2 ≤ d := by exact_mod_cast hdR.le
  have hdp : (0 : ℝ) < d := by linarith
  have hprod : (4 : ℝ) < (d : ℝ) * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hd)
  have hfrac : (2 : ℝ) / (d : ℝ) ≤ ε / 2 := (div_le_iff₀ hdp).mpr (by nlinarith)
  refine ⟨d, hdN, ?_⟩
  intro M
  obtain ⟨K, hK, hcount⟩ := uniform_power_bound d M hdN (ε / 2) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro F _hF _hchar P hD hM hP H hH
  have hpow : H ^ (2 / (d : ℝ) + ε / 2) ≤ H ^ ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact (hcount F P hD hM hP H hH).trans (mul_le_mul_of_nonneg_left hpow hK)

theorem uniform_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℕ, 2 ≤ d ∧ ∀ M : ℕ, ∃ H₀ : ℝ, 2 < H₀ ∧
      ∀ H ≥ H₀, ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      d ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ M →
      Irreducible P → ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ H ^ ε := by
  obtain ⟨d, hd, hdegrees⟩ := uniform_subpower_bound (ε / 2) (by positivity)
  refine ⟨d, hd, ?_⟩
  intro M
  obtain ⟨K, _hK, hcount⟩ := hdegrees M
  obtain ⟨H₀, hH₀, hsmall⟩ := eventual_power_absorption K (ε / 2) ε (by linarith)
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH F _hF _hchar P hD hM hP
  exact (hcount F P hD hM hP H (hH₀.trans_le hH)).trans (hsmall H hH)

end PaperP1.BoundedDegreePlaneCounts
