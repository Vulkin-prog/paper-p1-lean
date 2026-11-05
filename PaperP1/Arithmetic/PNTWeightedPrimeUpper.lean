module

public import PaperP1.Arithmetic.SharpPrimeCount
public import PaperP1.Arithmetic.WeightedPrimeSum

/-! # Weighted prime sums with arbitrary leading constant above one

The internally proved PNT supplies the true leading constant. A fixed positive
finite-prefix allowance is paid at the first weight; every cutoff and every
nonnegative decreasing weight follows that single choice.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNTWeightedPrimeUpper

open Finset Filter DefectCounting

theorem log_sum_eq_theta (Y : ℕ) :
    (∑ p ∈ smallPrimesUpTo Y, Real.log p) = Chebyshev.theta Y := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  apply sum_congr
  · ext p
    simp only [mem_smallPrimesUpTo, Nat.mem_primesLE, and_comm]
  · intro _ _
    rfl

theorem log_sum_upper_eventually (η : ℝ) (hη : 0 < η) :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y ≥ Y₀,
      (∑ p ∈ smallPrimesUpTo Y, Real.log p) ≤ (1 + η) * Y := by
  obtain ⟨f, hf, _hint, heq⟩ := PNT.chebyshev_asymptotic''
  have ht : Tendsto f atTop (nhds 0) := (Asymptotics.isLittleO_one_iff ℝ).mp (hf 1 zero_lt_one)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (ht.eventually (eventually_lt_nhds hη))
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp hnat
  refine ⟨max 2 Y₁, by omega, ?_⟩
  intro Y hY
  have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  rw [log_sum_eq_theta, heq Y hy]
  have hh := mul_le_mul_of_nonneg_left (hY₁ Y (by omega)).le hy.le
  nlinarith only [hh]

theorem global_log_sum_upper (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℕ,
      (∑ p ∈ smallPrimesUpTo Y, Real.log p) ≤ (1 + η) * Y + K := by
  obtain ⟨Y₀, _hY₀, hupper⟩ := log_sum_upper_eventually η hη
  let K := (∑ p ∈ smallPrimesUpTo Y₀, Real.log p) + 1
  have hs : 0 ≤ ∑ p ∈ smallPrimesUpTo Y₀, Real.log p := sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)
  have hK : 0 < K := by dsimp only [K]; linarith only [hs]
  refine ⟨K, hK, ?_⟩
  intro Y
  by_cases hY : Y₀ ≤ Y
  · exact (hupper Y hY).trans (le_add_of_nonneg_right hK.le)
  · have hsub : smallPrimesUpTo Y ⊆ smallPrimesUpTo Y₀ := by
      intro p hp
      obtain ⟨hpp, hpy⟩ := mem_smallPrimesUpTo.mp hp
      exact mem_smallPrimesUpTo.mpr ⟨hpp, by omega⟩
    have hh := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ Real.log_natCast_nonneg p)
    have hnon : 0 ≤ (1 + η) * (Y : ℝ) := by positivity
    dsimp only [K]
    linarith only [hh, hnon]

theorem weighted_upper (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ Y : ℕ, ∀ F : ℕ → ℝ,
      (∀ i : ℕ, 0 ≤ F (i + 1)) → Antitone (fun i : ℕ ↦ F (i + 1)) →
      (∑ p ∈ smallPrimesUpTo Y, Real.log p * F p) ≤
        (1 + η) * (∑ i ∈ range Y, F (i + 1)) + K * F 1 := by
  obtain ⟨K, hK, hprefix⟩ := global_log_sum_upper η hη
  refine ⟨K, hK, ?_⟩
  intro Y F hF hanti
  let f : ℕ → ℝ := fun i ↦ if Nat.Prime (i + 1) then Real.log (i + 1 : ℕ) else 0
  let c : ℕ → ℝ := fun i ↦ (1 + η) + if i = 0 then K else 0
  have hfc (k : ℕ) (_hk : k ≤ Y) : ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, c i := by
    by_cases hk : k = 0
    · simp only [hk, range_zero, sum_empty, le_refl]
    · have hk0 : 0 ∈ range k := mem_range.mpr (by omega)
      change (∑ i ∈ range k, if Nat.Prime (i + 1) then Real.log (i + 1 : ℕ) else 0) ≤ _
      rw [WeightedPrimeSum.sum_prime_sequence (fun p ↦ Real.log p) k]
      simpa [c, sum_add_distrib, hk0, mul_add, mul_comm] using hprefix k
  have hh := sum_mul_le_sum_mul_of_sum_range_le hfc hF
    (fun _ _ _ _ hij ↦ hanti hij)
  have hleft : (∑ i ∈ range Y, f i * F (i + 1)) =
      ∑ p ∈ smallPrimesUpTo Y, Real.log p * F p := by
    simpa only [f, ite_mul, zero_mul] using WeightedPrimeSum.sum_prime_sequence
      (fun p ↦ Real.log p * F p) Y
  rw [hleft] at hh
  have hright : (∑ i ∈ range Y, c i * F (i + 1)) ≤
      (1 + η) * (∑ i ∈ range Y, F (i + 1)) + K * F 1 := by
    simp only [c, add_mul, sum_add_distrib, ← mul_sum, ite_mul, zero_mul, sum_ite_eq', zero_add]
    split_ifs
    · exact le_rfl
    · exact add_le_add le_rfl (mul_nonneg hK.le (hF 0))
  exact hh.trans hright

end PaperP1.PNTWeightedPrimeUpper
