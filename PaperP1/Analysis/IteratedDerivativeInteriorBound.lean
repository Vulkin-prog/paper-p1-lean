module

public import PaperP1.Analysis.MonotoneDerivativeInteriorBound
public import PaperP1.Analysis.IteratedDerivativeMonotonicity
public import Mathlib.Tactic.Ring

/-! # Explicit higher derivative bounds on interior intervals

A unit first derivative and monotonicity of each controlled derivative give
an explicit geometric bound. The next-order sign will supply monotonicity.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IteratedDerivativeInteriorBound

open Set IteratedDerivativeMonotonicity MonotoneDerivativeInteriorBound
open scoped ContDiff

theorem trimmed_bound (f : ℝ → ℝ) (a b h : ℝ) (hh : 0 < h) (r : ℕ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hfirst : ∀ x ∈ Ioo a b, |deriv f x| ≤ 1)
    (hmono : ∀ j ≤ r, MonotoneOn (iteratedDeriv j f) (Ioo a b) ∨
      AntitoneOn (iteratedDeriv j f) (Ioo a b))
    (n : ℕ) (hn : n + 1 ≤ r) (x : ℝ)
    (hx : x ∈ Ioo (a + (n : ℝ) * h) (b - (n : ℝ) * h)) :
    |iteratedDeriv (n + 1) f x| ≤ (2 / h) ^ n := by
  have hall : ∀ m : ℕ, m + 1 ≤ r → ∀ y : ℝ,
      y ∈ Ioo (a + (m : ℝ) * h) (b - (m : ℝ) * h) →
        |iteratedDeriv (m + 1) f y| ≤ (2 / h) ^ m := by
    intro m
    induction m with
    | zero =>
      intro _hm y hy
      have hmem : y ∈ Ioo a b := by simpa only [Nat.cast_zero, zero_mul, add_zero, sub_zero] using hy
      simpa only [Nat.zero_add, iteratedDeriv_one, pow_zero] using hfirst y hmem
    | succ m ih =>
      intro hm y hy
      have hsmall : Ioo (a + (m : ℝ) * h) (b - (m : ℝ) * h) ⊆ Ioo a b := by
        intro v hv
        have hmh : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
        exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
      have hcentral : Icc (y - h) (y + h) ⊆ Ioo (a + (m : ℝ) * h) (b - (m : ℝ) * h) := by
        simp only [Nat.cast_add, Nat.cast_one] at hy
        intro v hv
        constructor <;> nlinarith [hy.1, hy.2, hv.1, hv.2]
      have hsub : Icc (y - h) (y + h) ⊆ Ioo a b := fun v hv ↦ hsmall (hcentral hv)
      have hfn := smooth_iterated f a b hf (m + 1)
      have hmonog : MonotoneOn (deriv (iteratedDeriv (m + 1) f)) (Ioo a b) ∨
          AntitoneOn (deriv (iteratedDeriv (m + 1) f)) (Ioo a b) := by
        have ht := hmono (m + 1 + 1) (by omega)
        rwa [iteratedDeriv_succ] at ht
      have hb := central_bound_on_open (iteratedDeriv (m + 1) f) a b y h ((2 / h) ^ m) hh
        (hfn.differentiableOn (by simp)) hsub
        (fun v hv ↦ ih (by omega) v (hcentral hv)) hmonog
      calc
        |iteratedDeriv (m.succ + 1) f y| = |deriv (iteratedDeriv (m + 1) f) y| := by
          rw [iteratedDeriv_succ]
        _ ≤ 2 * (2 / h) ^ m / h := hb
        _ = (2 / h) ^ m.succ := by rw [pow_succ]; ring
  exact hall n hn x hx

theorem interior_bound (f : ℝ → ℝ) (a b δ : ℝ) (hδ : 0 < δ) (r : ℕ)
    (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (hfirst : ∀ x ∈ Ioo a b, |deriv f x| ≤ 1)
    (hmono : ∀ j ≤ r, MonotoneOn (iteratedDeriv j f) (Ioo a b) ∨
      AntitoneOn (iteratedDeriv j f) (Ioo a b))
    (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) (x : ℝ)
    (hleft : a + δ ≤ x) (hright : x ≤ b - δ) :
    |iteratedDeriv j f x| ≤ (2 * ((r + 1 : ℕ) : ℝ) / δ) ^ (j - 1) := by
  let h : ℝ := δ / ((r + 1 : ℕ) : ℝ)
  have hpos : 0 < h := by positivity
  have hcast : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hmul : (((r + 1 : ℕ) : ℝ)) * h = δ := by
    dsimp only [h]
    field_simp [hcast.ne']
  have hnh : (((j - 1 : ℕ) : ℝ)) * h < δ := by
    calc
      _ < (((r + 1 : ℕ) : ℝ)) * h :=
        mul_lt_mul_of_pos_right (by exact_mod_cast (show j - 1 < r + 1 by omega)) hpos
      _ = δ := hmul
  have hmem : x ∈ Ioo (a + ((j - 1 : ℕ) : ℝ) * h) (b - ((j - 1 : ℕ) : ℝ) * h) :=
    ⟨by linarith, by linarith⟩
  have hc : 2 / h = 2 * ((r + 1 : ℕ) : ℝ) / δ := by
    dsimp only [h]
    field_simp [hδ.ne', hcast.ne']
  have hb := trimmed_bound f a b h hpos r hf hfirst hmono (j - 1) (by omega) x hmem
  simpa only [show j - 1 + 1 = j by omega, hc] using hb

end PaperP1.IteratedDerivativeInteriorBound
