module

public import PaperP1.Combinatorics.ComparableDyadicCover
public import PaperP1.Combinatorics.FiniteCoverCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact finite-cover power bounds on fixed comparable intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableCoverPower

open Finset PaperP1.ComparableDyadicCover

theorem power_bound (C N : ℕ) (hC : 1 ≤ C) (hN : 2 * C ≤ N) (S : Finset ℕ) (α G : ℝ)
    (hα : 0 ≤ α) (hG : 0 ≤ G) (hS : ∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N)
    (hcells : ∀ j ∈ indices C,
      ((S.filter fun n ↦ base C N j ≤ n ∧ n ≤ 2 * base C N j).card : ℝ) ≤
        (base C N j : ℝ) ^ α * G) :
    (S.card : ℝ) ≤ ((indices C).card : ℝ) * (distortion C : ℝ) ^ α * (N : ℝ) ^ α * G := by
  let F := fun j ↦ S.filter fun n ↦ base C N j ≤ n ∧ n ≤ 2 * base C N j
  have hcover : ∀ n ∈ S, ∃ j ∈ indices C, n ∈ F j := by
    intro n hn
    obtain ⟨j, hj, hbox⟩ := PaperP1.ComparableDyadicCover.cover C N n hC hN (hS n hn).1 (hS n hn).2
    exact ⟨j, hj, mem_filter.mpr ⟨hn, hbox⟩⟩
  have hF : ∀ j ∈ indices C,
      ((F j).card : ℝ) ≤ (distortion C : ℝ) ^ α * (N : ℝ) ^ α * G := by
    intro j hj
    have hb : (base C N j : ℝ) ≤ (distortion C : ℝ) * N := by
      exact_mod_cast (base_comparison C N j hC hN hj).2
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg _) hb hα
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hp
    exact (hcells j hj).trans (mul_le_mul_of_nonneg_right hp hG)
  have hcount := PaperP1.FiniteCoverCount.cardinal_le S (indices C) F
    ((distortion C : ℝ) ^ α * (N : ℝ) ^ α * G) hcover hF
  calc
    (S.card : ℝ) ≤ ((indices C).card : ℝ) * ((distortion C : ℝ) ^ α * (N : ℝ) ^ α * G) := hcount
    _ = _ := by ring

end PaperP1.ComparableCoverPower
