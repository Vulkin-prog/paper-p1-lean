module

public import PaperP1.Probability.UniformFinite
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring

/-! # Finite Fubini and independence for the actual normalized uniform weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformFubini

open Finset PaperP1.Algebra PaperP1.Probability

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

end PaperP1.UniformFubini
