module

public import PaperP1.Arithmetic.SmallPrimeBudget
public import PaperP1.Analysis.PartialPowerSum
public import Mathlib.Algebra.Order.Chebyshev

/-! # Elementary weighted prime sums from the finite primorial bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPrimeSum

open Finset PaperP1.DefectCounting PaperP1.SmallPrimeBudget PaperP1.PartialPowerSum

def primeSum (Y : ℕ) (σ : ℝ) : ℝ := ∑ p ∈ smallPrimesUpTo Y, (p : ℝ) ^ (-σ)

def logPrimeSum (Y : ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ smallPrimesUpTo Y, Real.log p * (p : ℝ) ^ (-σ)

theorem sum_prime_sequence (F : ℕ → ℝ) (Y : ℕ) :
    (∑ i ∈ range Y, if Nat.Prime (i + 1) then F (i + 1) else 0) =
      ∑ p ∈ smallPrimesUpTo Y, F p := by
  rw [← sum_filter]
  apply sum_bij (fun i _ ↦ i + 1)
  · intro i hi
    obtain ⟨hi, hp⟩ := mem_filter.mp hi
    exact mem_smallPrimesUpTo.mpr ⟨hp, by have := mem_range.mp hi; omega⟩
  · intro i _ j _ hij
    omega
  · intro p hp
    obtain ⟨hp, hpY⟩ := mem_smallPrimesUpTo.mp hp
    have hp0 := hp.pos
    refine ⟨p - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
    simpa only [Nat.sub_add_cancel hp0] using hp
  · intro i _
    rfl

theorem logPrimeSum_le_partialPower (Y : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) :
    logPrimeSum Y σ ≤ Real.log 4 * powerSum σ Y := by
  let f : ℕ → ℝ := fun i ↦ if Nat.Prime (i + 1) then Real.log (i + 1 : ℕ) else 0
  let g : ℕ → ℝ := fun i ↦ (i + 1 : ℝ) ^ (-σ)
  have hfc (k : ℕ) (_hk : k ≤ Y) :
      ∑ i ∈ range k, f i ≤ ∑ _i ∈ range k, Real.log 4 := by
    calc
      _ = ∑ p ∈ smallPrimesUpTo k, Real.log p := sum_prime_sequence (fun p ↦ Real.log p) k
      _ ≤ (k : ℝ) * Real.log 4 := prime_log_sum_le k
      _ = _ := by simp
  have hg : Antitone g := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact_mod_cast Nat.add_le_add_right hij 1
    · linarith
  have h := sum_mul_le_sum_mul_of_sum_range_le hfc
    (fun i ↦ Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ i + 1) (-σ))
    (fun _ _ _ _ hij ↦ hg hij)
  have hleft : (∑ i ∈ range Y, f i * g i) = logPrimeSum Y σ := by
    simpa only [f, g, ite_mul, zero_mul, Nat.cast_add, Nat.cast_one, logPrimeSum] using
      sum_prime_sequence (fun p ↦ Real.log p * (p : ℝ) ^ (-σ)) Y
  rw [hleft] at h
  simpa only [g, ← mul_sum, ← powerSum_eq_shifted] using h

theorem primeSum_le_power (Y σ : ℝ) (hY : 0 ≤ Y) (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    primeSum (Nat.floor Y) σ ≤ Y ^ (1 - σ) / (1 - σ) := by
  have hsub : smallPrimesUpTo (Nat.floor Y) ⊆ Finset.Icc 1 (Nat.floor Y) := by
    intro p hp
    obtain ⟨hp, hpY⟩ := mem_smallPrimesUpTo.mp hp
    exact mem_Icc.mpr ⟨hp.pos, hpY⟩
  calc
    _ ≤ powerSum σ (Nat.floor Y) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ (Nat.floor Y : ℝ) ^ (1 - σ) / (1 - σ) := powerSum_le σ hσ hσ1 _
    _ ≤ _ := div_le_div_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY) (by linarith)) (by linarith)

theorem logPrimeSum_le_power (Y σ : ℝ) (hY : 0 ≤ Y) (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    logPrimeSum (Nat.floor Y) σ ≤ Real.log 4 * (Y ^ (1 - σ) / (1 - σ)) := by
  calc
    _ ≤ Real.log 4 * powerSum σ (Nat.floor Y) := logPrimeSum_le_partialPower _ σ hσ
    _ ≤ Real.log 4 * ((Nat.floor Y : ℝ) ^ (1 - σ) / (1 - σ)) :=
      mul_le_mul_of_nonneg_left (powerSum_le σ hσ hσ1 _) (Real.log_nonneg (by norm_num))
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hY) (by linarith)) (by linarith))
      (Real.log_nonneg (by norm_num))

def smallPrimeConstant : ℝ := 4 * Real.log 4 + 64

theorem power_log_loss (Y p σ : ℝ) (hY : 0 < Y) (hp : 0 < p) :
    p ^ (-σ) * Real.log Y ≤ Real.log p * p ^ (-σ) +
      8 * Y ^ (1 / 8 : ℝ) * p ^ (-(σ + 1 / 8)) := by
  have hlog := Real.log_le_rpow_div (div_nonneg hY.le hp.le) (by norm_num : (0 : ℝ) < 1 / 8)
  rw [Real.log_div hY.ne' hp.ne'] at hlog
  have h := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hp.le (-σ))
  have heq : ((Y / p) ^ (1 / 8 : ℝ) / (1 / 8)) * p ^ (-σ) =
      8 * Y ^ (1 / 8 : ℝ) * p ^ (-(σ + 1 / 8)) := by
    rw [show -(σ + (1 / 8 : ℝ)) = -(1 / 8 : ℝ) + -σ by ring,
      Real.rpow_add hp, Real.div_rpow hY.le hp.le]
    simp only [div_eq_mul_inv]
    rw [← Real.rpow_neg hp.le]
    ring
  rw [heq] at h
  nlinarith

theorem logPrimeSum_le_uniform (Y σ : ℝ) (hY : 0 ≤ Y)
    (hσ : 0 ≤ σ) (hσ3 : σ ≤ 3 / 4) :
    logPrimeSum (Nat.floor Y) σ ≤ 4 * Real.log 4 * Y ^ (1 - σ) := by
  have hδ : 0 < 1 - σ := by linarith
  have hinv : 1 / (1 - σ) ≤ 4 := (div_le_iff₀ hδ).mpr (by linarith)
  calc
    _ ≤ Real.log 4 * (Y ^ (1 - σ) / (1 - σ)) := logPrimeSum_le_power Y σ hY hσ (by linarith)
    _ = (Real.log 4 * Y ^ (1 - σ)) * (1 / (1 - σ)) := by ring
    _ ≤ (Real.log 4 * Y ^ (1 - σ)) * 4 :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

theorem shifted_primeSum_le_uniform (Y σ : ℝ) (hY : 0 ≤ Y)
    (hσ : 0 ≤ σ) (hσ3 : σ ≤ 3 / 4) :
    primeSum (Nat.floor Y) (σ + 1 / 8) ≤ 8 * Y ^ (1 - (σ + 1 / 8)) := by
  have hδ : 0 < 1 - (σ + 1 / 8 : ℝ) := by linarith
  have hinv : 1 / (1 - (σ + 1 / 8 : ℝ)) ≤ 8 :=
    (div_le_iff₀ hδ).mpr (by linarith)
  calc
    _ ≤ Y ^ (1 - (σ + 1 / 8 : ℝ)) / (1 - (σ + 1 / 8 : ℝ)) :=
      primeSum_le_power Y (σ + 1 / 8) hY (by linarith) (by linarith)
    _ = Y ^ (1 - (σ + 1 / 8 : ℝ)) * (1 / (1 - (σ + 1 / 8 : ℝ))) := by ring
    _ ≤ Y ^ (1 - (σ + 1 / 8 : ℝ)) * 8 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

/-- A common constant on the whole compact exponent interval, without the PNT. -/
theorem primeSum_mul_log_le_uniform (Y σ : ℝ) (hY : 0 < Y)
    (hσ : 0 ≤ σ) (hσ3 : σ ≤ 3 / 4) :
    primeSum (Nat.floor Y) σ * Real.log Y ≤ smallPrimeConstant * Y ^ (1 - σ) := by
  have hterm (p : ℕ) (hp : p ∈ smallPrimesUpTo (Nat.floor Y)) :=
    power_log_loss Y p σ hY (by exact_mod_cast (mem_smallPrimesUpTo.mp hp).1.pos)
  have hpow : Y ^ (1 / 8 : ℝ) * Y ^ (1 - (σ + 1 / 8)) = Y ^ (1 - σ) := by
    rw [← Real.rpow_add hY]
    congr 1
    ring
  calc
    _ = ∑ p ∈ smallPrimesUpTo (Nat.floor Y), (p : ℝ) ^ (-σ) * Real.log Y := by rw [primeSum, sum_mul]
    _ ≤ ∑ p ∈ smallPrimesUpTo (Nat.floor Y),
        (Real.log p * (p : ℝ) ^ (-σ) + 8 * Y ^ (1 / 8 : ℝ) * (p : ℝ) ^ (-(σ + 1 / 8))) :=
      sum_le_sum hterm
    _ = logPrimeSum (Nat.floor Y) σ + 8 * Y ^ (1 / 8 : ℝ) *
        primeSum (Nat.floor Y) (σ + 1 / 8) := by
      simp only [logPrimeSum, primeSum, sum_add_distrib, mul_sum]
    _ ≤ 4 * Real.log 4 * Y ^ (1 - σ) + 8 * Y ^ (1 / 8 : ℝ) *
        (8 * Y ^ (1 - (σ + 1 / 8))) :=
      add_le_add (logPrimeSum_le_uniform Y σ hY.le hσ hσ3)
        (mul_le_mul_of_nonneg_left (shifted_primeSum_le_uniform Y σ hY.le hσ hσ3) (by positivity))
    _ = 4 * Real.log 4 * Y ^ (1 - σ) +
        64 * (Y ^ (1 / 8 : ℝ) * Y ^ (1 - (σ + 1 / 8))) := by ring
    _ = _ := by rw [hpow]; unfold smallPrimeConstant; ring

end PaperP1.WeightedPrimeSum
