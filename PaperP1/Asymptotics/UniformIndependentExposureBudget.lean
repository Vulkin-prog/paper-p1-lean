module

public import PaperP1.Model.IndependentExposureEulerBudget
public import PaperP1.Asymptotics.LogarithmicWordPowers

/-! # Weighted exceptional exposure rows have a common half-power budget before arbitrarily many preceding windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformIndependentExposureBudget

open Finset PaperP1.Model PaperP1.IndependentExposurePrimePool PaperP1.IndependentExposureEulerBudget
  PaperP1.CriticalBandScale

theorem uniform_row_constant (s : ℕ) (C M ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S : Finset ℕ, S ⊆ dyadicBlock N → S.card ≤ s → rowConstant N L S M ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  obtain ⟨NP, _hNP, hp⟩ := IndependentExposurePrimePool.uniform_bound s C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale upperScale_pos.le
    (M * Real.sqrt 3 / 2) 1 (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨4 + NP + NF + NG, by omega, ?_⟩
  intro N hN L hband S hS hs
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hwidth := (hg N (by omega) L hband).2.2.2.2.2
  have hcoef : (M * Real.sqrt 3 / 2) * ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have h := (le_abs_self _).trans (hf N (by omega) L hwidth)
    simpa only [pow_one, Nat.cast_add, Nat.cast_one] using h
  have hbase := hp N (by omega) L hband S hS hs
  have hrow : rowConstant N L S M = ((M * Real.sqrt 3 / 2) * ((L + 1 : ℕ) : ℝ)) *
      (N : ℝ) ^ (-(1 / 2 : ℝ)) * baseEuler S L := by
    unfold rowConstant
    rw [show Real.sqrt (3 * N : ℕ) = Real.sqrt 3 * Real.sqrt N by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num)],
      PaperP1.rpow_neg_one_half_eq_inv_sqrt _ hn.le]
    calc
      _ = ((M * Real.sqrt 3 / 2) * ((L + 1 : ℕ) : ℝ)) * (Real.sqrt N / (N : ℝ)) * baseEuler S L := by ring
      _ = _ := by rw [Real.sqrt_div_self]
  calc
    _ = _ := hrow
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hn.le _)) hbase
        (SmoothSquarefreeCount.eulerProduct_nonneg _ _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring

theorem uniform_budget (s : ℕ) (C M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S : Finset ℕ, S ⊆ dyadicBlock N → S.card ≤ s →
      ∀ w : ℕ → ℝ, (∀ x ∈ dyadicBlock N, w x ≤ M / N) →
      (∑ x ∈ dyadicBlock N, w x * windowEuler N L x) ≤ 3 * M * Real.exp 2 ∧
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N →
        (∑ x ∈ BranchingExceptional.badStarts N L (OldValuePrimeBudget.rawValues (S ∪ A) L), w x) ≤
          (N : ℝ) ^ (-1 / 2 + ε) * ∏ x ∈ A, windowEuler N L x := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_row_constant s C M ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨4 + NR + NG, by omega, ?_⟩
  intro N hN L hband S hS hs w hcap
  have hLN : L ≤ N := by have h := (hg N (by omega) L hband).2.2.2.1; omega
  refine ⟨weighted_first_moment N L (by omega) hLN w M hM hcap, ?_⟩
  intro A hA
  exact (weighted_bad_row S A N L (by omega) hLN hA w M hM hcap).trans
    (mul_le_mul_of_nonneg_right (hr N (by omega) L hband S hS hs)
      (prod_nonneg fun x _ ↦ by have h := window_one_le N L x; linarith))

end PaperP1.UniformIndependentExposureBudget
