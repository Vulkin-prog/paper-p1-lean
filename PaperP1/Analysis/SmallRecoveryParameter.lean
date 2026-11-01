module

public import PaperP1.Analysis.DisjointRecoveryParameters
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # A fixed integer recovery order with an arbitrarily small projection loss -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallRecoveryParameter

open PaperP1.DisjointRecoveryParameters

theorem power_order (d k : ℕ) (hd : 1 ≤ d) (hk : 2 ≤ k) :
    2 ≤ k ^ d ∧ parameter d (k ^ d) = (k : ℝ)⁻¹ := by
  have ht : 2 ≤ k ^ d := by
    calc
      2 ≤ k := hk
      _ = k ^ 1 := (pow_one _).symm
      _ ≤ k ^ d := Nat.pow_le_pow_right (by omega : 0 < k) hd
  refine ⟨ht, ?_⟩
  apply (pow_left_inj₀ (parameter_pos d (k ^ d) ht).le (by positivity : 0 ≤ (k : ℝ)⁻¹)
    (by omega : d ≠ 0)).mp
  rw [parameter_pow d (k ^ d) hd ht]
  simp only [inv_pow, Nat.cast_pow]

theorem exists_small (d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℕ, 2 ≤ t ∧ parameter d t < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (max 2 (1 / ε))
  have hk2 : 2 ≤ k := by exact_mod_cast (show (2 : ℝ) ≤ k from ((le_max_left _ _).trans_lt hk).le)
  obtain ⟨ht, hparameter⟩ := power_order d k hd hk2
  refine ⟨k ^ d, ht, ?_⟩
  rw [hparameter, ← one_div]
  have hkp : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (div_lt_iff₀ hkp).mpr
  have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hk)
  simpa only [mul_comm] using h

theorem exists_relative_cost (s : ℕ) (hs : 1 ≤ s) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ L : ℕ, 1 ≤ L →
      2 * (((s + 1) * (L + 1) : ℕ) : ℝ) * parameter s t ≤ η * L / 4 := by
  have hspos : (0 : ℝ) < (s + 1 : ℕ) := by positivity
  obtain ⟨t, ht, hsmall⟩ := exists_small s hs (η / (16 * (s + 1 : ℕ))) (by positivity)
  refine ⟨t, ht, ?_⟩
  intro L hL
  have hLcast : (1 : ℝ) ≤ L := by exact_mod_cast hL
  calc
    _ = (2 * (s + 1 : ℕ) * (L + 1 : ℕ)) * parameter s t := by push_cast; ring
    _ ≤ (2 * (s + 1 : ℕ) * (L + 1 : ℕ)) * (η / (16 * (s + 1 : ℕ))) :=
      mul_le_mul_of_nonneg_left hsmall.le (by positivity)
    _ = η * (L + 1 : ℕ) / 8 := by field_simp; norm_num
    _ ≤ η * L / 4 := by push_cast; nlinarith

end PaperP1.SmallRecoveryParameter
