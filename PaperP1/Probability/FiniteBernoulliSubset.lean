module

public import PaperP1.Probability.FiniteLaw
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # Independent Bernoulli selection of a finite coordinate set

The product weights, every fixed-subset inclusion probability and the
expected selected cardinality are finite identities. No independence claim
or event-probability formula is supplied as a premise.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteBernoulliSubset

open Finset PaperP1.Algebra PaperP1.Probability

variable {V : Type*} [Fintype V] [DecidableEq V]

def bitWeight (u : ℝ) (b : Bool) : ℝ := if b then u else 1 - u

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def weight (u : ℝ) (σ : V → Bool) : ℝ := ∏ v, bitWeight u (σ v)

def allTrue (A : Finset V) (σ : V → Bool) : ℝ := ∏ v ∈ A, bitValue (σ v)

def selected (σ : V → Bool) : Finset V := univ.filter fun v ↦ σ v = true

theorem sum_bitWeight (u : ℝ) : (∑ b : Bool, bitWeight u b) = 1 := by
  simp [bitWeight]

theorem weight_total (u : ℝ) : (∑ σ : V → Bool, weight u σ) = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp only [sum_bitWeight, prod_const_one]

omit [DecidableEq V] in
theorem weight_nonneg (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (σ : V → Bool) : 0 ≤ weight u σ := by
  unfold weight
  apply prod_nonneg
  intro v _
  cases h : σ v
  · simpa only [bitWeight, h, Bool.false_eq_true, reduceIte] using sub_nonneg.mpr hu1
  · simpa only [bitWeight, h, reduceIte] using hu0

def probability (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : FiniteProbability (V → Bool) where
  weight := weight u
  weight_nonneg := weight_nonneg u hu0 hu1
  total_weight := weight_total u

theorem allTrue_eq_indicator (A : Finset V) (σ : V → Bool) :
    allTrue A σ = if (∀ v ∈ A, σ v = true) then 1 else 0 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [allTrue]
  | @insert v A hv ih =>
    rw [allTrue, prod_insert hv, ← allTrue, ih]
    cases hs : σ v <;> simp [bitValue, hs]

theorem weight_mul_allTrue (u : ℝ) (A : Finset V) (σ : V → Bool) :
    weight u σ * allTrue A σ =
      ∏ v, bitWeight u (σ v) * (if v ∈ A then bitValue (σ v) else 1) := by
  unfold weight allTrue
  rw [prod_mul_distrib, prod_ite_mem_eq]

theorem expectation_allTrue (u : ℝ) (A : Finset V) :
    finiteExpectation (weight u) (allTrue A) = u ^ A.card := by
  unfold finiteExpectation
  simp_rw [weight_mul_allTrue]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) ↦
    bitWeight u b * (if v ∈ A then bitValue b else 1))]
  have hcell (v : V) : (∑ b : Bool, bitWeight u b * (if v ∈ A then bitValue b else 1)) =
      if v ∈ A then u else 1 := by
    by_cases hv : v ∈ A <;> simp [hv, bitWeight, bitValue]
  simp_rw [hcell]
  rw [prod_ite_mem_eq]
  simp

omit [DecidableEq V] in
theorem selected_card (σ : V → Bool) : (selected σ).card = ∑ v, (σ v).toNat := by
  unfold selected
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro v _
  cases σ v <;> simp

omit [DecidableEq V] in
theorem selected_card_real (σ : V → Bool) : ((selected σ).card : ℝ) = ∑ v, bitValue (σ v) := by
  rw [selected_card, Nat.cast_sum]
  apply sum_congr rfl
  intro v _
  cases σ v <;> simp [bitValue]

theorem expectation_selected_card (u : ℝ) :
    finiteExpectation (weight u) (fun σ : V → Bool ↦ ((selected σ).card : ℝ)) = Fintype.card V * u := by
  simp_rw [selected_card_real]
  rw [finiteExpectation_sum]
  have hsingle (v : V) : finiteExpectation (weight u) (fun σ : V → Bool ↦ bitValue (σ v)) = u := by
    have hf : allTrue ({v} : Finset V) = (fun σ : V → Bool ↦ bitValue (σ v)) := by
      funext σ
      exact prod_singleton _ _
    rw [← hf]
    simpa only [card_singleton, pow_one] using expectation_allTrue u {v}
  simp only [hsingle, sum_const, nsmul_eq_mul, card_univ]

end PaperP1.FiniteBernoulliSubset
