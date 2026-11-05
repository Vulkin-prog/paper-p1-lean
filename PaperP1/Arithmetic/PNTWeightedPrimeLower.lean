module

public import PaperP1.Arithmetic.PNTWeightedPrimeUpper

/-! # Weighted prime lower bounds with the true leading constant

A single finite-prefix allowance works before all cutoffs and every
nonnegative decreasing weight, by finite summation by parts.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNTWeightedPrimeLower

open Finset Filter DefectCounting

theorem log_sum_lower_eventually (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y ≥ Y₀,
      (1 - η) * Y ≤ ∑ p ∈ smallPrimesUpTo Y, Real.log p := by
  obtain ⟨f, hf, _hint, heq⟩ := PNT.chebyshev_asymptotic''
  have ht : Tendsto f atTop (nhds 0) := (Asymptotics.isLittleO_one_iff ℝ).mp (hf 1 zero_lt_one)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (ht.eventually (eventually_gt_nhds (by linarith only [hη] : -η < 0)))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hnat
  refine ⟨max 2 Y₁, by omega, ?_⟩
  intro Y hY
  have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  rw [PNTWeightedPrimeUpper.log_sum_eq_theta, heq Y hy]
  have hh := mul_le_mul_of_nonneg_left (hY₁ Y (by omega)).le hy.le
  nlinarith only [hh]

theorem global_log_sum_lower (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℕ,
      (1 - η) * Y - K ≤ ∑ p ∈ smallPrimesUpTo Y, Real.log p := by
  obtain ⟨Y₀, _hY₀, hlower⟩ := log_sum_lower_eventually η hη
  let K : ℝ := Y₀ + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro Y
  by_cases hY : Y₀ ≤ Y
  · exact (sub_le_self _ hK.le).trans (hlower Y hY)
  · have hYY : (Y : ℝ) ≤ Y₀ := by exact_mod_cast (show Y ≤ Y₀ by omega)
    have hs : 0 ≤ ∑ p ∈ smallPrimesUpTo Y, Real.log p :=
      sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
    have hy : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
    dsimp only [K]
    nlinarith only [hYY, hs, hy, hη]

theorem weighted_lower (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℕ, ∀ F : ℕ → ℝ,
      (∀ i : ℕ, 0 ≤ F (i + 1)) → Antitone (fun i : ℕ ↦ F (i + 1)) →
      (1 - η) * (∑ i ∈ range Y, F (i + 1)) - K * F 1 ≤
        ∑ p ∈ smallPrimesUpTo Y, Real.log p * F p := by
  obtain ⟨K, hK, hprefix⟩ := global_log_sum_lower η hη
  refine ⟨K, hK, ?_⟩
  intro Y F hF hanti
  let f : ℕ → ℝ := fun i ↦ if Nat.Prime (i + 1) then Real.log (i + 1 : ℕ) else 0
  let c : ℕ → ℝ := fun i ↦ (1 - η) - if i = 0 then K else 0
  have hcf (k : ℕ) (_hk : k ≤ Y) : ∑ i ∈ range k, c i ≤ ∑ i ∈ range k, f i := by
    by_cases hk : k = 0
    · simp only [hk, range_zero, sum_empty, le_refl]
    · have hk0 : 0 ∈ range k := mem_range.mpr (by omega)
      change _ ≤ ∑ i ∈ range k, if Nat.Prime (i + 1) then Real.log (i + 1 : ℕ) else 0
      rw [WeightedPrimeSum.sum_prime_sequence (fun p ↦ Real.log p) k]
      simpa [c, sum_sub_distrib, hk0, mul_sub, mul_comm] using hprefix k
  have hh := sum_mul_le_sum_mul_of_sum_range_le hcf hF
    (fun _ _ _ _ hij ↦ hanti hij)
  have hright : (∑ i ∈ range Y, f i * F (i + 1)) =
      ∑ p ∈ smallPrimesUpTo Y, Real.log p * F p := by
    simpa only [f, ite_mul, zero_mul] using WeightedPrimeSum.sum_prime_sequence
      (fun p ↦ Real.log p * F p) Y
  rw [hright] at hh
  have hleft : (1 - η) * (∑ i ∈ range Y, F (i + 1)) - K * F 1 ≤
      ∑ i ∈ range Y, c i * F (i + 1) := by
    by_cases hY : Y = 0
    · simp only [hY, range_zero, sum_empty, mul_zero, zero_sub]
      exact neg_nonpos.mpr (mul_nonneg hK.le (hF 0))
    · have hY0 : 0 ∈ range Y := mem_range.mpr (by omega)
      simp [c, sub_mul, sum_sub_distrib, ← mul_sum, hY0]
  exact hleft.trans hh

end PaperP1.PNTWeightedPrimeLower
