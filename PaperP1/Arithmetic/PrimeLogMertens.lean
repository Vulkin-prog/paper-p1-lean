module

public import PaperP1.Arithmetic.MangoldtFloorBudget
public import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! # A uniform constant error for the actual weighted prime-logarithm sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeLogMertens

open Finset
open scoped ArithmeticFunction

def primePowerTerm (n : ℕ) : ℝ := (if n.Prime then 0 else Λ n) / n

theorem primePowerTerm_nonneg (n : ℕ) : 0 ≤ primePowerTerm n := by
  unfold primePowerTerm
  positivity [ArithmeticFunction.vonMangoldt_nonneg (n := n)]

theorem primePowerTerm_summable : Summable primePowerTerm := by
  change Summable (fun n : ℕ ↦ (if n.Prime then 0 else Λ n) / n)
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [ArithmeticFunction.vonMangoldt.residueClass,
    Subsingleton.elim (fun n : ℕ ↦ (n : ZMod 1)) (fun _ ↦ 0), Set.indicator_univ, Set.ofPred_true] using h

def primePowerTotal : ℝ := ∑' n, primePowerTerm n

theorem primePowerTotal_nonneg : 0 ≤ primePowerTotal := tsum_nonneg primePowerTerm_nonneg

def coefficient (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

def weightedPrimes (N : ℕ) : ℝ := ∑ n ∈ range (N + 1), coefficient n

def partialSum (x : ℝ) : ℝ := ∑ n ∈ Icc 0 ⌊x⌋₊, coefficient n

def budget : ℝ := Real.log 4 + primePowerTotal + 6

theorem budget_pos : 0 < budget := by
  have ht := primePowerTotal_nonneg
  have hl := Real.log_natCast_nonneg 4
  unfold budget
  norm_num at hl
  linarith

theorem weighted_split (N : ℕ) :
    MangoldtFloorBudget.weightedMangoldt N = weightedPrimes N + ∑ n ∈ range (N + 1), primePowerTerm n := by
  rw [MangoldtFloorBudget.weightedMangoldt, weightedPrimes, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _hn
  by_cases hp : n.Prime
  · simp only [coefficient, primePowerTerm, hp, ite_true, ArithmeticFunction.vonMangoldt_apply_prime hp,
      zero_div, add_zero]
  · simp only [coefficient, primePowerTerm, hp, ite_false, zero_add]

theorem primePower_partial_le (N : ℕ) : ∑ n ∈ range (N + 1), primePowerTerm n ≤ primePowerTotal :=
  primePowerTerm_summable.sum_le_tsum _ (fun n _hn ↦ primePowerTerm_nonneg n)

theorem natural_bounds (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - (primePowerTotal + 1) ≤ weightedPrimes N ∧
      weightedPrimes N ≤ Real.log N + (Real.log 4 + 4) := by
  have hm := MangoldtFloorBudget.weightedMangoldt_bounds N hN
  have hsplit := weighted_split N
  have ht := primePower_partial_le N
  have hnonneg : 0 ≤ ∑ n ∈ range (N + 1), primePowerTerm n :=
    sum_nonneg (fun n _hn ↦ primePowerTerm_nonneg n)
  constructor <;> linarith

theorem natural_error (N : ℕ) (hN : 1 ≤ N) :
    |weightedPrimes N - Real.log N| ≤ Real.log 4 + primePowerTotal + 5 := by
  have hb := natural_bounds N hN
  have ht := primePowerTotal_nonneg
  have hl := Real.log_natCast_nonneg 4
  norm_num at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem prefix_eq_weighted_floor (x : ℝ) : partialSum x = weightedPrimes ⌊x⌋₊ := by
  have hset : Icc 0 ⌊x⌋₊ = range (⌊x⌋₊ + 1) := by
    apply Finset.ext
    intro n
    rw [mem_Icc, mem_range]
    omega
  exact congrArg (fun s : Finset ℕ ↦ ∑ n ∈ s, coefficient n) hset

theorem prefix_error (x : ℝ) (hx : 2 ≤ x) : |partialSum x - Real.log x| ≤ budget := by
  have hfloor : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr (by linarith)
  have hfpos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  have hflow : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hftwo : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
    have hnext := Nat.lt_floor_add_one x
    have hf : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hfloor
    linarith
  have hlo : Real.log (⌊x⌋₊ : ℝ) ≤ Real.log x := Real.log_le_log hfpos hflow
  have hhi : Real.log x ≤ Real.log 2 + Real.log (⌊x⌋₊ : ℝ) := by
    have h := Real.log_le_log (by linarith : 0 < x) hftwo
    rwa [Real.log_mul (by norm_num) (ne_of_gt hfpos)] at h
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have he := natural_error ⌊x⌋₊ hfloor
  rw [prefix_eq_weighted_floor]
  unfold budget
  exact abs_le.mpr ⟨by linarith [(abs_le.mp he).1], by linarith [(abs_le.mp he).2]⟩

end PaperP1.PrimeLogMertens
