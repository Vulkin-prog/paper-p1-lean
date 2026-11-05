module

public import PaperP1.Analysis.IteratedDerivativeMonotonicity
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Actual local Taylor coefficients and explicit uniform remainder bounds

All coefficients use ordinary derivatives at an actual interior anchor. The
closed-segment Taylor theorem is connected to those exact local derivatives.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualTaylorRemainderBound

open Set Finset
open scoped ContDiff Interval

def jet (f : ℝ → ℝ) (n : ℕ) (c x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), iteratedDeriv k f c * (x - c) ^ k / (k.factorial : ℝ)

theorem jet_self (f : ℝ → ℝ) (n : ℕ) (c : ℝ) : jet f n c c = f c := by
  unfold jet
  calc
    _ = ∑ k ∈ range (n + 1), if k = 0 then f c else 0 := by
      apply sum_congr rfl
      intro k _hk
      by_cases hk : k = 0
      · subst k
        simp
      · simp [hk]
    _ = f c := by simp

theorem within_eq_jet (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (hs : UniqueDiffOn ℝ s)
    (c x : ℝ) (hf : ContDiffAt ℝ ∞ f c) (hc : c ∈ s) :
    taylorWithinEval f n s c x = jet f n c x := by
  rw [taylor_within_apply, jet]
  apply sum_congr rfl
  intro k _hk
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.of_le (by simp)) hc]
  simp only [smul_eq_mul]
  ring

theorem factorial_divisor_bound (y M : ℝ) (n : ℕ) (hy : |y| ≤ M) :
    |y / (n.factorial : ℝ)| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg y).trans hy
  have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    have hn : 1 ≤ n.factorial := Nat.factorial_pos n
    exact_mod_cast hn
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (n.factorial : ℝ) from Nat.cast_nonneg _)]
  exact (div_le_div_of_nonneg_right hy (Nat.cast_nonneg _)).trans (div_le_self hM hfac)

theorem remainder_bound (f : ℝ → ℝ) (a b : ℝ) (hf : ContDiffOn ℝ ∞ f (Ioo a b))
    (n : ℕ) (c x : ℝ) (hc : c ∈ Ioo a b) (hx : x ∈ Ioo a b)
    (M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hdist : |x - c| ≤ δ)
    (hder : ∀ y ∈ Ioo a b, |iteratedDeriv (n + 1) f y| ≤ M) :
    |f x - jet f n c x| ≤ M * δ ^ (n + 1) := by
  by_cases hcx : c = x
  · subst x
    rw [jet_self, sub_self, abs_zero]
    exact mul_nonneg hM (pow_nonneg hδ _)
  · have hsub : uIcc c x ⊆ Ioo a b := by
      intro y hy
      rcases le_total c x with h | h
      · rw [uIcc_of_le h] at hy
        exact ⟨hc.1.trans_le hy.1, hy.2.trans_lt hx.2⟩
      · rw [uIcc_of_ge h] at hy
        exact ⟨hx.1.trans_le hy.1, hy.2.trans_lt hc.2⟩
    have hclosed : ContDiffOn ℝ (n + 1) f (uIcc c x) := (hf.of_le (by simp)).mono hsub
    obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hcx hclosed
    have hTaylor : taylorWithinEval f n (uIcc c x) c x = jet f n c x :=
      within_eq_jet f n _ (uniqueDiffOn_uIcc hcx) c x
        (hf.contDiffAt (isOpen_Ioo.mem_nhds hc)) left_mem_uIcc
    rw [hTaylor] at heq
    have hξmem : ξ ∈ Ioo a b := hsub ⟨hξ.1.le, hξ.2.le⟩
    have hnum : |iteratedDeriv (n + 1) f ξ * (x - c) ^ (n + 1)| ≤ M * δ ^ (n + 1) := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hder ξ hξmem) (pow_le_pow_left₀ (abs_nonneg _) hdist _)
        (pow_nonneg (abs_nonneg _) _) hM
    rw [heq]
    exact factorial_divisor_bound _ _ (n + 1) hnum

end PaperP1.ActualTaylorRemainderBound
