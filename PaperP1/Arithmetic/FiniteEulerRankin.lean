module

public import PaperP1.Analysis.RankinComparison
public import PaperP1.Arithmetic.DefectCounting

/-! # A finite Rankin bound for weighted sets of distinct integer factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteEulerRankin

open Finset PaperP1.RankinComparison

def admissibleSupports (P : Finset ℕ) (X : ℝ) : Finset (Finset ℕ) :=
  P.powerset.filter fun S ↦ (↑(S.prod id) : ℝ) ≤ X

def weightedCount (P : Finset ℕ) (X a : ℝ) : ℝ :=
  ∑ S ∈ admissibleSupports P X, a ^ S.card

theorem mem_admissibleSupports {P S : Finset ℕ} {X : ℝ} :
    S ∈ admissibleSupports P X ↔ S ⊆ P ∧ (↑(S.prod id) : ℝ) ≤ X := by
  simp only [admissibleSupports, mem_filter, mem_powerset]

theorem rankin_term (P S : Finset ℕ) (X a s : ℝ) (hP : ∀ p ∈ P, 1 ≤ p)
    (hS : S ∈ admissibleSupports P X) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    a ^ S.card ≤ X ^ s * ∏ p ∈ S, (a * (p : ℝ) ^ (-s)) := by
  obtain ⟨hSP, hSX⟩ := mem_admissibleSupports.mp hS
  have hprod : 0 < S.prod id := by
    apply prod_pos
    intro p hp
    exact zero_lt_one.trans_le (hP p (hSP hp))
  have hprodR : (0 : ℝ) < S.prod id := by exact_mod_cast hprod
  have hX : 0 ≤ X := hprodR.le.trans hSX
  have hquot : 1 ≤ X / (↑(S.prod id) : ℝ) := by
    apply (le_div_iff₀ hprodR).mpr
    simpa using hSX
  have hone := Real.one_le_rpow hquot hs
  rw [Real.div_rpow hX hprodR.le, div_eq_mul_inv, ← Real.rpow_neg hprodR.le] at hone
  have hfactor : (∏ p ∈ S, (a * (p : ℝ) ^ (-s))) = a ^ S.card * (↑(S.prod id) : ℝ) ^ (-s) := by
    rw [prod_mul_distrib, prod_const, cast_prod_rpow]
  calc
    _ = a ^ S.card * 1 := (mul_one _).symm
    _ ≤ a ^ S.card * (X ^ s * (↑(S.prod id) : ℝ) ^ (-s)) :=
      mul_le_mul_of_nonneg_left hone (pow_nonneg ha _)
    _ = _ := by rw [hfactor]; ring

theorem weightedCount_le_euler (P : Finset ℕ) (X a s : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hX : 0 ≤ X) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    weightedCount P X a ≤ X ^ s * ∏ p ∈ P, (1 + a * (p : ℝ) ^ (-s)) := by
  calc
    _ ≤ ∑ S ∈ admissibleSupports P X, X ^ s * ∏ p ∈ S, (a * (p : ℝ) ^ (-s)) :=
      sum_le_sum (fun S hS ↦ rankin_term P S X a s hP hS ha hs)
    _ = X ^ s * ∑ S ∈ admissibleSupports P X, ∏ p ∈ S, (a * (p : ℝ) ^ (-s)) :=
      (mul_sum _ _ _).symm
    _ ≤ X ^ s * ∑ S ∈ P.powerset, ∏ p ∈ S, (a * (p : ℝ) ^ (-s)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hX s)
      apply sum_le_sum_of_subset_of_nonneg (fun S hS ↦ mem_powerset.mpr (mem_admissibleSupports.mp hS).1)
      intro S _ _
      exact prod_nonneg (fun p _ ↦ mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    _ = _ := by rw [← prod_one_add]

theorem weightedCount_le_exp (P : Finset ℕ) (X a s : ℝ)
    (hP : ∀ p ∈ P, 1 ≤ p) (hX : 0 ≤ X) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    weightedCount P X a ≤ X ^ s * Real.exp (a * ∑ p ∈ P, (p : ℝ) ^ (-s)) := by
  calc
    _ ≤ X ^ s * ∏ p ∈ P, (1 + a * (p : ℝ) ^ (-s)) := weightedCount_le_euler P X a s hP hX ha hs
    _ ≤ X ^ s * Real.exp (∑ p ∈ P, a * (p : ℝ) ^ (-s)) := mul_le_mul_of_nonneg_left
      (Real.prod_one_add_le_exp_sum _ (fun p ↦ mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg p) _)))
      (Real.rpow_nonneg hX s)
    _ = _ := by rw [← mul_sum]

end PaperP1.FiniteEulerRankin
