module

public import PaperP1.Probability.UniformFinite
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! # Finite Fubini and independence for the actual normalized uniform weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformFubini

open Finset PaperP1.Algebra PaperP1.Probability

local instance uniformFubiniDecidable (P : Prop) : Decidable P := Classical.propDecidable P

abbrev average {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) : ℝ :=
  finiteExpectation (uniformFiniteProbability Ω).weight f

theorem product {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ξ] [Nonempty Ξ]
    (f : Ω × Ξ → ℝ) :
    average f = average (fun ω ↦ average (fun ξ ↦ f (ω, ξ))) := by
  simp only [average, uniformFiniteExpectation_eq, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type, ← sum_div]
  ring

theorem independent_product {κ Ω : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [Nonempty Ω] (f : κ → Ω → ℝ) :
    average (fun ω : κ → Ω ↦ ∏ i, f i (ω i)) = ∏ i, average (f i) := by
  simp only [average, uniformFiniteExpectation_eq, Fintype.card_fun, Nat.cast_pow]
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_div_distrib, Finset.prod_const, card_univ]

theorem congr {Ω : Type*} [Fintype Ω] [Nonempty Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω = g ω) : average f = average g := congrArg average (funext h)

theorem nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ average f :=
  sum_nonneg fun ω _ ↦ mul_nonneg ((uniformFiniteProbability Ω).weight_nonneg ω) (h ω)

theorem constant {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    average (fun _ : Ω ↦ c) = c := by
  rw [average, finiteExpectation_const, (uniformFiniteProbability Ω).total_weight, one_mul]

theorem equiv {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ξ] [Nonempty Ξ]
    (e : Ω ≃ Ξ) (f : Ξ → ℝ) : average (fun ω ↦ f (e ω)) = average f := by
  simp only [average, uniformFiniteExpectation_eq, Fintype.card_congr e, Equiv.sum_comp]

theorem condition_first {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ξ] [Nonempty Ξ]
    (f : Ω × Ξ → ℝ) (a : Ω) :
    average (fun p : Ω × Ξ ↦ if p.1 = a then f p else 0) /
      average (fun p : Ω × Ξ ↦ if p.1 = a then (1 : ℝ) else 0) =
      average (fun ξ ↦ f (a, ξ)) := by
  classical
  rw [product, product]
  have hn (ω : Ω) : average (fun ξ : Ξ ↦ if ω = a then f (ω, ξ) else 0) =
      if ω = a then average (fun ξ ↦ f (a, ξ)) else 0 := by
    by_cases h : ω = a
    · subst ω
      simp only [ite_true]
    · simp only [h, ite_false, constant]
  have hd (ω : Ω) : average (fun _ : Ξ ↦ if ω = a then (1 : ℝ) else 0) =
      if ω = a then (1 : ℝ) else 0 := constant _
  simp_rw [hn, hd]
  simp only [average, uniformFiniteExpectation_eq, sum_ite_eq', mem_univ, ite_true]
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem set_average {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ξ] [Nonempty Ξ]
    (f : Ω × Ξ → ℝ) (s : Set Ω) :
    average (fun p : Ω × Ξ ↦ if p.1 ∈ s then average (fun ξ ↦ f (p.1, ξ)) else 0) =
      average (fun p : Ω × Ξ ↦ if p.1 ∈ s then f p else 0) := by
  classical
  rw [product, product]
  apply UniformFubini.congr
  intro ω
  by_cases h : ω ∈ s
  · simp only [h, ite_true, constant]
  · simp only [h, ite_false, constant]

end PaperP1.UniformFubini
