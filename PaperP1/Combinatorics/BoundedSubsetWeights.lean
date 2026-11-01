module

public import PaperP1.Analysis.ExponentialPowerSum
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # A uniform finite bound for colored subsets of bounded size -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedSubsetWeights

open Finset

variable {ι : Type*}

def boundedSubsets (P : Finset ι) (m : ℕ) : Finset (Finset ι) := P.powerset.filter (fun S ↦ S.card ≤ m)

def weightSum (P : Finset ι) (b : ℝ) (m : ℕ) : ℝ := ∑ S ∈ boundedSubsets P m, b ^ S.card

theorem mem_boundedSubsets (P S : Finset ι) (m : ℕ) :
    S ∈ boundedSubsets P m ↔ S ⊆ P ∧ S.card ≤ m := by simp [boundedSubsets]

theorem powerset_weight_identity (P : Finset ι) (x : ℝ) :
    (∑ S ∈ P.powerset, x ^ S.card) = (1 + x) ^ P.card := by
  have h := prod_one_add (f := fun _ : ι ↦ x) P
  simpa only [prod_const] using h.symm

theorem weightSum_mul_le (P : Finset ι) (b t : ℝ) (m : ℕ)
    (hb : 0 ≤ b) (ht : 0 < t) (htone : t ≤ 1) :
    weightSum P b m * t ^ m ≤ (1 + b * t) ^ P.card := by
  rw [weightSum, sum_mul]
  calc
    _ ≤ ∑ S ∈ boundedSubsets P m, (b * t) ^ S.card := by
      apply sum_le_sum
      intro S hS
      have hcard := ((mem_boundedSubsets P S m).mp hS).2
      have hpow : t ^ m ≤ t ^ S.card := pow_le_pow_of_le_one ht.le htone hcard
      simpa only [mul_pow] using mul_le_mul_of_nonneg_left hpow (pow_nonneg hb S.card)
    _ ≤ ∑ S ∈ P.powerset, (b * t) ^ S.card := by
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ ↦ by positivity)
    _ = _ := powerset_weight_identity P (b * t)

theorem weightSum_le (P : Finset ι) (b K : ℝ) (m : ℕ) (hb : 1 ≤ b) (hK : 1 ≤ K) :
    weightSum P b m ≤ (b * K) ^ m * Real.exp ((P.card : ℝ) / K) := by
  have hbpos : 0 < b := by linarith
  have hKpos : 0 < K := by linarith
  have hprod : 1 ≤ b * K := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hK)]
  have ht : 0 < (b * K)⁻¹ := by positivity
  have htone : (b * K)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hprod
  have h := weightSum_mul_le P b (b * K)⁻¹ m hbpos.le ht htone
  have hbase : b * (b * K)⁻¹ = K⁻¹ := by field_simp
  rw [hbase] at h
  have hexp : (1 + K⁻¹) ^ P.card ≤ Real.exp ((P.card : ℝ) / K) := by
    calc
      _ ≤ (Real.exp K⁻¹) ^ P.card := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [Real.add_one_le_exp K⁻¹]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1
  have h' := h.trans hexp
  have hp : 0 < (b * K) ^ m := by positivity
  have hcancel : weightSum P b m * (b * K)⁻¹ ^ m * (b * K) ^ m = weightSum P b m := by
    rw [inv_pow]
    field_simp
  calc
    _ = weightSum P b m * (b * K)⁻¹ ^ m * (b * K) ^ m := hcancel.symm
    _ ≤ Real.exp ((P.card : ℝ) / K) * (b * K) ^ m := mul_le_mul_of_nonneg_right h' hp.le
    _ = _ := mul_comm _ _

/-- No condition such as m <= card(P)/2 is required. -/
theorem weightSum_le_of_card_le (P : Finset ι) (b K : ℝ) (m : ℕ)
    (hb : 1 ≤ b) (hK : 1 ≤ K) (hcard : (P.card : ℝ) ≤ K * m) :
    weightSum P b m ≤ (b * Real.exp 1 * K) ^ m := by
  have hKpos : 0 < K := by linarith
  have hratio : (P.card : ℝ) / K ≤ m := (div_le_iff₀ hKpos).mpr (by nlinarith)
  calc
    _ ≤ (b * K) ^ m * Real.exp ((P.card : ℝ) / K) := weightSum_le P b K m hb hK
    _ ≤ (b * K) ^ m * Real.exp m := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hratio) (by positivity)
    _ = _ := by simp only [mul_pow, ← Real.exp_nat_mul, mul_one]; ring

end PaperP1.BoundedSubsetWeights
