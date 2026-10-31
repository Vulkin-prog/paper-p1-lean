module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-
Adapted from PaperC/Diophantine/PellInput.lean, by Vulkin-prog, Apache-2.0.
Source commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 99025d6105dc01e60fb722a94a81e6e8d96c65aa.
Only finite-count predicates and exact equation/height definitions; historical literature interfaces excluded.
-/

@[expose] public section

namespace PaperP1.PellInput

/--
`HasAtMostSolutionsReal P B` says that every finite family of solutions of
`P` has cardinality at most the real number `B`.
-/
def HasAtMostSolutionsReal
    {α : Type*} [DecidableEq α]
    (P : α → Prop) (B : ℝ) : Prop :=
  ∀ s : Finset α, (∀ x ∈ s, P x) → (s.card : ℝ) ≤ B

/-- The equation `A z² - C w² = e`. -/
def pellEquation
    (A C : ℕ) (e : ℤ) (solution : ℤ × ℤ) : Prop :=
  (A : ℤ) * solution.1 ^ 2 -
      (C : ℤ) * solution.2 ^ 2 =
    e

/-- The original equation together with a symmetric integral height box. -/
def pellBox
    (A C : ℕ) (e : ℤ) (H : ℕ)
    (solution : ℤ × ℤ) : Prop :=
  pellEquation A C e solution ∧
    solution.1.natAbs ≤ H ∧
    solution.2.natAbs ≤ H

/-- The normalized generalized Pell equation and its height box. -/
def generalizedPellBox
    (D : ℕ) (M : ℤ) (H : ℕ)
    (solution : ℤ × ℤ) : Prop :=
  solution.1 ^ 2 -
      (D : ℤ) * solution.2 ^ 2 =
    M ∧
    solution.1.natAbs ≤ H ∧
    solution.2.natAbs ≤ H


end PaperP1.PellInput

