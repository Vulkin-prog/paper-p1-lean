module

public import PaperP1.Analysis.AnalyticWronskianNormalization
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # The classical partial-Wronskian Chebyshev criterion

Nonvanishing of all actual initial Wronskians supplies the recursive pivots.
The conclusion counts every finite distinct zero population of a combination.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolyaChebyshevCriterion

open Set AnalyticWronskianProduct AnalyticWronskianNormalization
open scoped ContDiff

def initialFamily {n : ℕ} (f : Fin n → ℝ → ℝ) (j : ℕ) (hj : j ≤ n) : Fin j → ℝ → ℝ :=
  fun i ↦ f (Fin.castLE hj i)

def PartialNonzero {n : ℕ} (f : Fin n → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ j : ℕ, ∀ hj : j ≤ n, 0 < j → ∀ x ∈ s, wronskian j (initialFamily f j hj) x ≠ 0

theorem admissible_of_partial (n : ℕ) (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b)) (hW : PartialNonzero f (Ioo a b)) :
    RecursiveChebyshev.Admissible n f a b := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hpivot : ∀ x ∈ Ioo a b, f 0 x ≠ 0 := by
      intro x hx
      have hh := hW 1 (by omega) (by decide) x hx
      simpa [initialFamily, wronskian, jetMatrix, Matrix.det_unique, Fin.default_eq_zero] using hh
    have hg : ∀ i : Fin n, ContDiffOn ℝ ∞ (RecursiveChebyshev.normalizedDerivative f i) (Ioo a b) := by
      intro i
      exact ((hf i.succ).div (hf 0) hpivot).deriv_of_isOpen isOpen_Ioo (by simp)
    have hWG : PartialNonzero (RecursiveChebyshev.normalizedDerivative f) (Ioo a b) := by
      intro j hj hjpos x hx
      have hj₁ : j + 1 ≤ n + 1 := by omega
      let F := initialFamily f (j + 1) hj₁
      have hF : ∀ i, ContDiffOn ℝ (j + 1) (F i) (Ioo a b) := by
        intro i
        exact (hf (Fin.castLE hj₁ i)).of_le (by simp)
      have hFzero : ∀ t ∈ Ioo a b, F 0 t ≠ 0 := by
        intro t ht
        exact hpivot t ht
      have hh := hW (j + 1) hj₁ (by omega) x hx
      have he := wronskian_normalized j F (Ioo a b) isOpen_Ioo hF hFzero x hx
      change wronskian (j + 1) F x ≠ 0 at hh
      rw [he] at hh
      exact right_ne_zero_of_mul hh
    exact ⟨fun i ↦ (hf i).differentiableOn (by simp), hpivot,
      ih (RecursiveChebyshev.normalizedDerivative f) hg hWG⟩

theorem card_lt (n : ℕ) (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b)) (hW : PartialNonzero f (Ioo a b))
    (c : Fin n → ℝ) (hc : c ≠ 0) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ RecursiveChebyshev.combination f c x = 0) : S.card < n :=
  RecursiveChebyshev.card_lt a b f (admissible_of_partial n a b f hf hW) c hc S hS

theorem coefficients_eq_zero (n : ℕ) (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b)) (hW : PartialNonzero f (Ioo a b))
    (S : Finset ℝ) (hcard : n ≤ S.card) (c : Fin n → ℝ)
    (hS : ∀ x ∈ S, x ∈ Ioo a b ∧ RecursiveChebyshev.combination f c x = 0) : c = 0 :=
  RecursiveChebyshev.coefficients_eq_zero a b f (admissible_of_partial n a b f hf hW) S hcard c hS

theorem evaluation_injective (n : ℕ) (a b : ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo a b)) (hW : PartialNonzero f (Ioo a b))
    (S : Finset ℝ) (hcard : n ≤ S.card) (hS : ∀ x ∈ S, x ∈ Ioo a b) :
    Function.Injective (fun c : Fin n → ℝ ↦ fun x : S ↦ RecursiveChebyshev.combination f c x) :=
  RecursiveChebyshev.evaluation_injective a b f (admissible_of_partial n a b f hf hW) S hcard hS

end PaperP1.PolyaChebyshevCriterion
