module

public import PaperP1.Asymptotics.ModerateCertificateAsymptotic
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # A finite exact schedule from exponent zero to one half -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountSchedule

open Finset Filter

def x (J j : ℕ) : ℝ := (j : ℝ) / (2 * J)

def A (J j : ℕ) : ℝ := (2 * J : ℝ) / (j + 1 : ℕ)

def step (J : ℕ) : ℝ := 1 / (2 * J : ℝ)

theorem exists_small_step (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ step J < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n + 1, by omega, ?_⟩
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  exact (one_div_le_one_div_of_le hnpos (by
    change ((n + 1 : ℕ) : ℝ) ≤ 2 * (n + 1 : ℕ)
    nlinarith)).trans_lt (by simpa only [Nat.cast_add, Nat.cast_one] using hn)

theorem x_zero (J : ℕ) : x J 0 = 0 := by simp only [x, Nat.cast_zero, zero_div]

theorem x_last (J : ℕ) (hJ : 0 < J) : x J J = 1 / 2 := by
  have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  unfold x
  field_simp

theorem x_succ (J j : ℕ) : x J (j + 1) = x J j + step J := by
  simp only [x, step, Nat.cast_add, Nat.cast_one, add_div]

theorem x_le_half (J j : ℕ) (hJ : 0 < J) (hj : j ≤ J) : x J j ≤ 1 / 2 := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hjr : (j : ℝ) ≤ J := by exact_mod_cast hj
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * J)).mpr
  nlinarith only [hjr]

theorem exponent_ge_two (J j : ℕ) (hj : j < J) : 2 ≤ A J j := by
  have hd : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have hjr : ((j + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast (show j + 1 ≤ J by omega)
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hjr]

theorem inverse_exponent (J j : ℕ) : 1 / A J j = x J (j + 1) := by
  simp only [A, x, one_div_div]

theorem pair_cost (J j r : ℕ) (η : ℝ) :
    (1 - x J j + η) + (x J (j + 1) + η) + ((r : ℝ) / 2 + η) =
      ((r + 2 : ℕ) : ℝ) / 2 + step J + 3 * η := by
  rw [x_succ]
  push_cast
  ring

theorem old_cost (J j r : ℕ) (η : ℝ) (hJ : 0 < J) (hj : j < J) :
    (x J (j + 1) + η) + (((r + 1 : ℕ) : ℝ) / 2 + η) ≤
      ((r + 2 : ℕ) : ℝ) / 2 + 2 * η := by
  have hx := x_le_half J (j + 1) hJ (by omega)
  push_cast
  linarith only [hx]

theorem factor_absorption (K p ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, K * (N : ℝ) ^ p ≤ (N : ℝ) ^ (p + ε) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (PaperP1.ModerateCertificateAsymptotic.constant_le_power_eventually K ε hε)
  refine ⟨max 2 N₀, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ p := mul_le_mul_of_nonneg_right (hN₀ N (by omega)) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem centre_count (C : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : Finset ℕ, (∀ n ∈ G, n ≤ C * N) →
      (G.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, hN₀⟩ := factor_absorption (C + 1) 1 ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN G hG
  have hsub : G ⊆ range (C * N + 1) := fun n hn ↦ mem_range.mpr (by have := hG n hn; omega)
  have hcard : (G.card : ℝ) ≤ C * N + 1 := by exact_mod_cast (card_le_card hsub).trans_eq (card_range _)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  calc
    (G.card : ℝ) ≤ (C + 1 : ℝ) * N := hcard.trans (by nlinarith only [hn])
    _ ≤ (N : ℝ) ^ (1 + ε) := by simpa only [Real.rpow_one] using hN₀ N (by omega)

end PaperP1.HalfCountSchedule
