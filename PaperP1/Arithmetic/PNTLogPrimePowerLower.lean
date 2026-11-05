module

public import PaperP1.Arithmetic.PNTWeightedPrimeLower

/-! # Uniform logarithmically weighted prime-power minorants

The leading constant and finite-prefix allowance are selected before the
power exponent and integer cutoff. An exact integral lower comparison
retains the real power of the actual integer endpoint.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNTLogPrimePowerLower

open Finset Set MeasureTheory DefectCounting

def weight (σ : ℝ) (n : ℕ) : ℝ := ((max 2 n : ℕ) : ℝ) ^ (-σ)

theorem weight_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ weight σ n :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem weight_antitone (σ : ℝ) (hσ : 0 ≤ σ) : Antitone (weight σ) := by
  intro m n hmn
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < max 2 m by omega))
    (by exact_mod_cast max_le_max le_rfl hmn) (neg_nonpos.mpr hσ)

theorem weight_one_le (σ : ℝ) (hσ : 0 ≤ σ) : weight σ 1 ≤ 1 := by
  change (2 : ℝ) ^ (-σ) ≤ 1
  simpa only [Real.rpow_zero] using
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (neg_nonpos.mpr hσ)

theorem uniform_log_power_lower (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 ≤ σ → ∀ Y : ℕ,
      (1 - η) * (∑ i ∈ range Y, weight σ (i + 1)) - C ≤ WeightedPrimeSum.logPrimeSum Y σ := by
  obtain ⟨C, hC, hw⟩ := PNTWeightedPrimeLower.weighted_lower η hη
  refine ⟨C, hC, ?_⟩
  intro σ hσ Y
  have hh := hw Y (weight σ) (fun i ↦ weight_nonneg σ (i + 1))
    (fun i j hij ↦ weight_antitone σ hσ (Nat.add_le_add_right hij 1))
  have hid : (∑ p ∈ smallPrimesUpTo Y, Real.log p * weight σ p) = WeightedPrimeSum.logPrimeSum Y σ := by
    apply sum_congr rfl
    intro p hp
    rw [weight, max_eq_right (mem_smallPrimesUpTo.mp hp).1.two_le]
  rw [hid] at hh
  have he := mul_le_mul_of_nonneg_left (weight_one_le σ hσ) hC.le
  nlinarith only [hh, he]

theorem integer_sum_lower (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (Y : ℕ) (hY : 2 ≤ Y) :
    ((Y : ℝ) ^ δ - (2 : ℝ) ^ δ) / δ ≤ ∑ i ∈ range Y, weight (1 - δ) (i + 1) := by
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-(1 - δ))) (Set.Icc 2 Y) := by
    intro x hx y _hyl hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith only [hx.1] : 0 < x) hxy (by linarith only [hδ1])
  have hi := hanti.integral_le_sum_Ico hY
  rw [integral_rpow (Or.inl (by linarith only [hδ] : -1 < -(1 - δ))),
    show -(1 - δ) + 1 = δ by ring] at hi
  calc
    _ ≤ ∑ n ∈ Finset.Ico 2 Y, (n : ℝ) ^ (-(1 - δ)) := hi
    _ = ∑ n ∈ Finset.Ico 2 Y, weight (1 - δ) n := by
      apply sum_congr rfl
      intro n hn
      rw [weight, max_eq_right (mem_Ico.mp hn).1]
    _ ≤ ∑ n ∈ Finset.Icc 1 Y, weight (1 - δ) n := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hl, hu⟩ := mem_Ico.mp hn
        exact mem_Icc.mpr ⟨by omega, by omega⟩
      · intro n _ _
        exact weight_nonneg _ n
    _ = _ := by
      symm
      apply sum_bij (fun i _ ↦ i + 1)
      · intro i hi
        exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hi; omega⟩
      · intro i _ j _ hij
        omega
      · intro n hn
        obtain ⟨hl, hu⟩ := mem_Icc.mp hn
        exact ⟨n - 1, mem_range.mpr (by omega), by omega⟩
      · intro i _
        rfl

theorem uniform_lower (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ Y : ℕ, 2 ≤ Y →
      (1 - η) * (((Y : ℝ) ^ δ - (2 : ℝ) ^ δ) / δ) - C ≤
        WeightedPrimeSum.logPrimeSum Y (1 - δ) := by
  obtain ⟨C, hC, hw⟩ := uniform_log_power_lower η hη
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ1 Y hY
  have hs := mul_le_mul_of_nonneg_left (integer_sum_lower δ hδ hδ1 Y hY)
    (by linarith only [hη1] : 0 ≤ 1 - η)
  exact (sub_le_sub_right hs C).trans (hw (1 - δ) (by linarith only [hδ1]) Y)

theorem uniform_exponential_lower (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ Y : ℕ, 2 ≤ Y →
      (1 - η) * ((Real.exp (δ * Real.log Y) - 2) / δ) - C ≤
        WeightedPrimeSum.logPrimeSum Y (1 - δ) := by
  obtain ⟨C, hC, hw⟩ := uniform_lower η hη hη1
  refine ⟨C, hC, ?_⟩
  intro δ hδ hδ1 Y hY
  have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have htwo : (2 : ℝ) ^ δ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hδ1
  have hs := div_le_div_of_nonneg_right (sub_le_sub_left htwo ((Y : ℝ) ^ δ)) hδ.le
  have hm := mul_le_mul_of_nonneg_left hs (by linarith only [hη1] : 0 ≤ 1 - η)
  have hh := (sub_le_sub_right hm C).trans (hw δ hδ hδ1 Y hY)
  simpa only [Real.rpow_def_of_pos hy, mul_comm δ (Real.log Y)] using hh

end PaperP1.PNTLogPrimePowerLower
