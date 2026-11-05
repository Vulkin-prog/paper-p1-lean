module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Tactic.Push

/-! # Actual derivative monotonicity from the next actual derivative sign -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IteratedDerivativeMonotonicity

open Set
open scoped ContDiff

theorem nonneg_or_nonpos (g : ℝ → ℝ) (s : Set ℝ)
    (hsg : ∀ x ∈ s, ∀ y ∈ s, SignType.sign (g x) = SignType.sign (g y)) :
    (∀ x ∈ s, 0 ≤ g x) ∨ (∀ x ∈ s, g x ≤ 0) := by
  classical
  by_cases hpos : ∀ x ∈ s, 0 ≤ g x
  · exact Or.inl hpos
  · push Not at hpos
    obtain ⟨x, hx, hneg⟩ := hpos
    apply Or.inr
    intro y hy
    apply sign_nonpos_iff.mp
    rw [hsg y hy x hx]
    exact sign_nonpos_iff.mpr hneg.le

theorem smooth_iterated (f : ℝ → ℝ) (a b : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) (Ioo a b) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioo (by simp)

theorem monotone_or_antitone (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b)) (n : ℕ)
    (hsg : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b,
      SignType.sign (iteratedDeriv (n + 1) f x) = SignType.sign (iteratedDeriv (n + 1) f y)) :
    MonotoneOn (iteratedDeriv n f) (Ioo a b) ∨ AntitoneOn (iteratedDeriv n f) (Ioo a b) := by
  have hfn := smooth_iterated f a b hf n
  have hd : DifferentiableOn ℝ (iteratedDeriv n f) (interior (Ioo a b)) := by
    rw [interior_Ioo]
    exact hfn.differentiableOn (by simp)
  rcases nonneg_or_nonpos (iteratedDeriv (n + 1) f) (Ioo a b) hsg with hp | hn
  · apply Or.inl
    apply monotoneOn_of_deriv_nonneg (convex_Ioo a b) hfn.continuousOn hd
    intro x hx
    rw [interior_Ioo] at hx
    rw [← iteratedDeriv_succ]
    exact hp x hx
  · apply Or.inr
    apply antitoneOn_of_deriv_nonpos (convex_Ioo a b) hfn.continuousOn hd
    intro x hx
    rw [interior_Ioo] at hx
    rw [← iteratedDeriv_succ]
    exact hn x hx

end PaperP1.IteratedDerivativeMonotonicity
