module

public import PaperP1.Analysis.BothGraphDerivativeFormulas
public import PaperP1.Analysis.PolynomialQuotientControl
public import PaperP1.Algebra.GraphControlExceptions

/-! # Actual graph derivative signs through the specified control order

The domain is open for actual derivative identities and preconnected for signs.
All orders zero through r are retained; an order r+1 use must raise the control.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphControlledDerivatives

open MvPolynomial Set GraphControlPolynomials BothGraphDerivativeFormulas

theorem coordinate_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (s : Set ℝ)
    (hs : IsPreconnected s) (φ : Fin 2 → ℝ → ℝ)
    (hc : ContinuousOn (fun t ↦ fun j ↦ φ j t) s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (i : Fin 2) (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) :
    SignType.sign (φ i t) = SignType.sign (φ i u) := by
  have hA : ∀ v ∈ s, eval (fun j ↦ φ j v) (1 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro v _hv
    simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]
  fin_cases i
  · have hh := PolynomialQuotientControl.sign_constant P (family P r) 1 0 s hs
      (fun v ↦ fun j ↦ φ j v) hc hcurve hA (Sum.inl 8) t u ht hu
    simpa [family, static] using hh
  · have hh := PolynomialQuotientControl.sign_constant P (family P r) 1 0 s hs
      (fun v ↦ fun j ↦ φ j v) hc hcurve hA (Sum.inl 9) t u ht hu
    simpa [family, static] using hh

theorem first_zero_or_nowhere_zero (P : MvPolynomial (Fin 2) ℝ) (r : ℕ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hφ : GraphTangentEvaluation.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r) (n : ℕ) (hn : n < r) :
    (∀ t ∈ s, iteratedDeriv (n + 1) (φ 1) t = 0) ∨
      (∀ t ∈ s, iteratedDeriv (n + 1) (φ 1) t ≠ 0) := by
  have hh := PolynomialQuotientControl.zero_or_nowhere_zero P (family P r) (pderiv 1 P)
    (2 * n + 1) s (fun t ↦ fun j ↦ φ j t) hcurve hφ.1 (Sum.inr (0, ⟨n, hn⟩))
  rcases hh with hz | hz
  · exact Or.inl (fun t ht ↦ (first P φ s hs hφ n ht).trans (hz t ht))
  · exact Or.inr (fun t ht ↦ by rw [first P φ s hs hφ n ht]; exact hz t ht)

theorem second_zero_or_nowhere_zero (P : MvPolynomial (Fin 2) ℝ) (r : ℕ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hs : IsOpen s)
    (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r) (n : ℕ) (hn : n < r) :
    (∀ t ∈ s, iteratedDeriv (n + 1) (φ 0) t = 0) ∨
      (∀ t ∈ s, iteratedDeriv (n + 1) (φ 0) t ≠ 0) := by
  have hh := PolynomialQuotientControl.zero_or_nowhere_zero P (family P r) (pderiv 0 P)
    (2 * n + 1) s (fun t ↦ fun j ↦ φ j t) hcurve hφ.1 (Sum.inr (1, ⟨n, hn⟩))
  rcases hh with hz | hz
  · exact Or.inl (fun t ht ↦ (second P φ s hs hφ n ht).trans (hz t ht))
  · exact Or.inr (fun t ht ↦ by rw [second P φ s hs hφ n ht]; exact hz t ht)

theorem first_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hφ : GraphTangentEvaluation.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (n : ℕ) (hn : n < r) (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) :
    SignType.sign (iteratedDeriv (n + 1) (φ 1) t) =
      SignType.sign (iteratedDeriv (n + 1) (φ 1) u) := by
  rw [first P φ s hs hφ n ht, first P φ s hs hφ n hu]
  exact PolynomialQuotientControl.sign_constant P (family P r) (pderiv 1 P) (2 * n + 1)
    s hconn (fun v ↦ fun j ↦ φ j v) (continuousOn_first P φ s hφ) hcurve hφ.1
    (Sum.inr (0, ⟨n, hn⟩)) t u ht hu

theorem second_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (n : ℕ) (hn : n < r) (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) :
    SignType.sign (iteratedDeriv (n + 1) (φ 0) t) =
      SignType.sign (iteratedDeriv (n + 1) (φ 0) u) := by
  rw [second P φ s hs hφ n ht, second P φ s hs hφ n hu]
  exact PolynomialQuotientControl.sign_constant P (family P r) (pderiv 0 P) (2 * n + 1)
    s hconn (fun v ↦ fun j ↦ φ j v) (continuousOn_second P φ s hφ) hcurve hφ.1
    (Sum.inr (1, ⟨n, hn⟩)) t u ht hu

theorem first_all_orders_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hφ : GraphTangentEvaluation.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (n : ℕ) (hn : n ≤ r) (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) :
    SignType.sign (iteratedDeriv n (φ 1) t) = SignType.sign (iteratedDeriv n (φ 1) u) := by
  cases n with
  | zero =>
    simpa only [iteratedDeriv_zero] using
      coordinate_sign P r s hconn φ (continuousOn_first P φ s hφ) hcurve 1 t u ht hu
  | succ n => exact first_sign P r φ s hs hconn hφ hcurve n (by omega) t u ht hu

theorem second_all_orders_sign (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hconn : IsPreconnected s)
    (hφ : TransposedNormalizedGraphPiece.Trajectory P φ s)
    (hcurve : ∀ t ∈ s, eval (fun j ↦ φ j t) P = 0 ∧
      (fun j ↦ φ j t) ∉ GraphControlExceptions.points P r)
    (n : ℕ) (hn : n ≤ r) (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) :
    SignType.sign (iteratedDeriv n (φ 0) t) = SignType.sign (iteratedDeriv n (φ 0) u) := by
  cases n with
  | zero =>
    simpa only [iteratedDeriv_zero] using
      coordinate_sign P r s hconn φ (continuousOn_second P φ s hφ) hcurve 0 t u ht hu
  | succ n => exact second_sign P r φ s hs hconn hφ hcurve n (by omega) t u ht hu

end PaperP1.GraphControlledDerivatives
