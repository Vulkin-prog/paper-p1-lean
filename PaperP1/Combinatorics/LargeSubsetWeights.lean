module

public import PaperP1.Combinatorics.BoundedSubsetWeights
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A finite exponential tilt for large subsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeSubsetWeights

open Finset

variable {ι : Type*}

def subsets (P : Finset ι) (K : ℕ) : Finset (Finset ι) :=
  P.powerset.filter fun I ↦ K < I.card

def weightSum (P : Finset ι) (x : ℝ) (K : ℕ) : ℝ := ∑ I ∈ subsets P K, x ^ I.card

theorem weightSum_nonneg (P : Finset ι) (x : ℝ) (hx : 0 ≤ x) (K : ℕ) :
    0 ≤ weightSum P x K := sum_nonneg (fun _ _ ↦ pow_nonneg hx _)

theorem tilt_product_bound (P : Finset ι) (x t : ℝ) (K : ℕ) (hx : 0 ≤ x) (ht : 1 ≤ t) :
    weightSum P x K * t ^ K ≤ (1 + x * t) ^ P.card := by
  rw [weightSum, sum_mul]
  calc
    _ ≤ ∑ I ∈ subsets P K, (x * t) ^ I.card := by
      apply sum_le_sum
      intro I hI
      have hcard := (mem_filter.mp hI).2
      have hpow : t ^ K ≤ t ^ I.card := pow_le_pow_right₀ ht hcard.le
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hpow (pow_nonneg hx I.card)
    _ ≤ ∑ I ∈ P.powerset, (x * t) ^ I.card :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ pow_nonneg (mul_nonneg hx (by linarith)) _)
    _ = _ := PaperP1.BoundedSubsetWeights.powerset_weight_identity P (x * t)

theorem tilt_exponential_bound (P : Finset ι) (x t : ℝ) (K : ℕ) (hx : 0 ≤ x) (ht : 1 ≤ t) :
    weightSum P x K ≤ Real.exp ((P.card : ℝ) * x * t) / t ^ K := by
  have htpos : 0 < t := by linarith
  apply (le_div_iff₀ (pow_pos htpos K)).mpr
  calc
    _ ≤ (1 + x * t) ^ P.card := tilt_product_bound P x t K hx ht
    _ ≤ (Real.exp (x * t)) ^ P.card := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [Real.add_one_le_exp (x * t)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem optimized_bound (P : Finset ι) (p Λ : ℝ) (K : ℕ)
    (hp : 0 ≤ p) (hΛ : 0 < Λ) (hK : 0 < K) (hsize : 2 * Λ ≤ (K : ℝ))
    (hmean : (P.card : ℝ) * p ≤ Λ) :
    weightSum P (2 * p) K ≤ Real.exp (-(K : ℝ) * Real.log ((K : ℝ) / (2 * Real.exp 1 * Λ))) := by
  let t : ℝ := (K : ℝ) / (2 * Λ)
  have ht : 1 ≤ t := (le_div_iff₀ (by positivity : 0 < 2 * Λ)).mpr (by simpa only [one_mul] using hsize)
  have htpos : 0 < t := by linarith
  have hkr : (0 : ℝ) < K := by exact_mod_cast hK
  have hexponent : (P.card : ℝ) * (2 * p) * t ≤ K := by
    have hmul := mul_le_mul_of_nonneg_right hmean (show 0 ≤ 2 * t by positivity)
    have heq : Λ * (2 * t) = K := by dsimp [t]; field_simp
    nlinarith only [hmul, heq]
  have hratio : (K : ℝ) / (2 * Real.exp 1 * Λ) = t / Real.exp 1 := by dsimp [t]; field_simp
  have hlog : Real.log ((K : ℝ) / (2 * Real.exp 1 * Λ)) = Real.log t - 1 := by
    rw [hratio, Real.log_div htpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
  calc
    _ ≤ Real.exp ((P.card : ℝ) * (2 * p) * t) / t ^ K :=
      tilt_exponential_bound P (2 * p) t K (by positivity) ht
    _ ≤ Real.exp (K : ℝ) / t ^ K :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hexponent) (pow_nonneg htpos.le K)
    _ = _ := by
      have hpower : t ^ K = Real.exp ((K : ℝ) * Real.log t) := by
        rw [Real.exp_nat_mul, Real.exp_log htpos]
      rw [hpower, ← Real.exp_sub, hlog]
      congr 1
      ring

theorem log_budget_bound (P : Finset ι) (p Λ : ℝ) (K N : ℕ)
    (hp : 0 ≤ p) (hΛ : 0 < Λ) (hK : 0 < K) (hN : 0 < N)
    (hsize : 2 * Λ ≤ (K : ℝ)) (hmean : (P.card : ℝ) * p ≤ Λ)
    (hbudget : 3 * Real.log N ≤ (K : ℝ) * Real.log ((K : ℝ) / (2 * Real.exp 1 * Λ))) :
    weightSum P (2 * p) K ≤ (N : ℝ) ^ (-3 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ Real.exp (-(K : ℝ) * Real.log ((K : ℝ) / (2 * Real.exp 1 * Λ))) :=
      optimized_bound P p Λ K hp hΛ hK hsize hmean
    _ ≤ Real.exp (-3 * Real.log N) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.rpow_def_of_pos hn]; congr 1; ring

end PaperP1.LargeSubsetWeights
