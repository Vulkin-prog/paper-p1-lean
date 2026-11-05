module

public import PaperP1.Arithmetic.PNTWeightedPrimeUpper
public import PaperP1.Arithmetic.PrimeHarmonicUpper

/-! # Uniform prime-power and Euler estimates with the true leading prime constant

Every nonnegative exponent uses the same finite-prefix constant after eta>0
is fixed. The remaining integer reciprocal-logarithmic sum is explicit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNTPrimePowerUpper

open Finset DefectCounting

def weight (σ : ℝ) (n : ℕ) : ℝ :=
  (((max 2 n : ℕ) : ℝ) ^ (-σ)) / Real.log (max 2 n : ℕ)

theorem weight_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ weight σ n := by
  apply div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ max 2 n by omega))

theorem weight_antitone (σ : ℝ) (hσ : 0 ≤ σ) : Antitone (weight σ) := by
  intro m n hmn
  have hm : (1 : ℝ) < (max 2 m : ℕ) := by exact_mod_cast (show 1 < max 2 m by omega)
  have hn : (1 : ℝ) < (max 2 n : ℕ) := by exact_mod_cast (show 1 < max 2 n by omega)
  have hmax : ((max 2 m : ℕ) : ℝ) ≤ (max 2 n : ℕ) := by exact_mod_cast max_le_max le_rfl hmn
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith only [hm] : (0 : ℝ) < (max 2 m : ℕ))
    hmax (neg_nonpos.mpr hσ)
  have hlog := Real.log_le_log (by linarith only [hm] : (0 : ℝ) < (max 2 m : ℕ)) hmax
  exact (div_le_div_of_nonneg_right hp (Real.log_pos hn).le).trans
    (div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.log_pos hm) hlog)

theorem weight_one_le (σ : ℝ) (hσ : 0 ≤ σ) : weight σ 1 ≤ 1 / Real.log 2 := by
  change (2 : ℝ) ^ (-σ) / Real.log 2 ≤ 1 / Real.log 2
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (neg_nonpos.mpr hσ)
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simpa only [Real.rpow_zero] using hh

theorem prime_weight_identity (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    Real.log p * weight σ p = (p : ℝ) ^ (-σ) := by
  rw [weight, max_eq_right hp.two_le]
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  field_simp

theorem uniform_prime_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 ≤ σ → ∀ Y : ℕ,
      (∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-σ)) ≤
        C + (1 + η) * (∑ i ∈ range Y, weight σ (i + 1)) := by
  obtain ⟨K, hK, hw⟩ := PNTWeightedPrimeUpper.weighted_upper η hη
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := K / Real.log 2
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro σ hσ Y
  have hh := hw Y (weight σ) (fun i ↦ weight_nonneg σ (i + 1))
    (fun i j hij ↦ weight_antitone σ hσ (Nat.add_le_add_right hij 1))
  have hid : (∑ p ∈ smallPrimesUpTo Y, Real.log p * weight σ p) =
      ∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-σ) := by
    apply sum_congr rfl
    intro p hp
    exact prime_weight_identity σ (mem_smallPrimesUpTo.mp hp).1
  rw [hid] at hh
  calc
    _ ≤ (1 + η) * (∑ i ∈ range Y, weight σ (i + 1)) + K * weight σ 1 := hh
    _ ≤ (1 + η) * (∑ i ∈ range Y, weight σ (i + 1)) + K * (1 / Real.log 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (weight_one_le σ hσ) hK.le)
    _ = _ := by dsimp only [C]; ring

theorem uniform_euler_upper (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 ≤ σ → ∀ Y : ℕ,
      (∏ p ∈ smallPrimesUpTo Y, (1 + (p : ℝ) ^ (-σ))) ≤
        Real.exp (C + (1 + η) * (∑ i ∈ range Y, weight σ (i + 1))) := by
  obtain ⟨C, hC, hp⟩ := uniform_prime_upper η hη
  refine ⟨C, hC, ?_⟩
  intro σ hσ Y
  calc
    _ ≤ ∏ p ∈ smallPrimesUpTo Y, Real.exp ((p : ℝ) ^ (-σ)) := by
      gcongr with p _
      simpa only [add_comm] using Real.add_one_le_exp ((p : ℝ) ^ (-σ))
    _ = Real.exp (∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-σ)) := by rw [Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (hp σ hσ Y)

theorem uniform_pivot_count (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y : ℕ, 2 ≤ Y → ∀ σ : ℝ, 1 / 2 ≤ σ →
      ((OddPrimePivot.pivotValues X Y).card : ℝ) ≤ (X : ℝ) ^ σ *
        Real.exp (C + (1 + η) * (∑ i ∈ range Y, weight σ (i + 1))) := by
  obtain ⟨C, hC, he⟩ := uniform_euler_upper η hη
  refine ⟨C, hC, ?_⟩
  intro X Y hY σ hσ
  have hsub : ((OddPrimePivot.pivotValues X Y).card : ℝ) ≤ (SmallKernelCount.smallKernelValues Y 1 X).card := by
    exact_mod_cast card_le_card (PolylogPivotExceptions.pivot_subset_small_kernel X Y (by omega))
  have hbase := SmallKernelCount.card_smallKernelValues_le_euler Y 1 X σ hσ
  have hone : PartialPowerSum.powerSum σ 1 = 1 := by simp [PartialPowerSum.powerSum]
  rw [hone, mul_one] at hbase
  have hEuler := he σ (by linarith only [hσ]) Y
  change SmallKernelCount.eulerProduct Y σ ≤ _ at hEuler
  exact hsub.trans (hbase.trans (mul_le_mul_of_nonneg_left hEuler (Real.rpow_nonneg (Nat.cast_nonneg X) _)))

end PaperP1.PNTPrimePowerUpper
