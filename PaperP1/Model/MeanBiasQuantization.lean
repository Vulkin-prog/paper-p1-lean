module

public import PaperP1.Model.RegularSetFinite
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # The exact integral quantum of the mean bias

The identity is finite and requires no critical-band or approximation input.
The critical-band comparison only supplies the explicit size of its quantum.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MeanBiasQuantization

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.Arithmetic
  PaperP1.Affine PaperP1.CountObservables PaperP1.Probability

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def deficiency (x L : ℕ) : ℕ := L - Module.finrank F₂ (squareClassSpace x L)

def localMultiplicity (x L : ℕ) : ℕ := if 0 < infiniteMarginal x L then 2 ^ deficiency x L else 0

def coefficient (x L : ℕ) : ℤ := (localMultiplicity x L : ℤ) - 1

def bias (G : Finset ℕ) (L : ℕ) : ℤ := ∑ x ∈ G, coefficient x L

theorem multiplicity_source (x : ℕ) {L : ℕ} (hL : 0 < L) :
    localMultiplicity x L =
      (if Compatible (startSystem (x + L) x L) (startRhs L) then 1 else 0) * 2 ^ deficiency x L := by
  simp only [localMultiplicity, infiniteMarginal_pos_iff_compatible hL (le_refl (x + L))]
  split_ifs <;> simp

theorem nominal_times_multiplicity {x L : ℕ} (hx : 0 < x) (hL : 0 < L) :
    infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ * (localMultiplicity x L : ℝ) := by
  have hp : 0 ≤ infiniteMarginal x L := by
    rw [infiniteMarginal_eq_finite (le_refl (x + L))]
    exact exactMarginal_nonneg _ _ _
  by_cases hpos : 0 < infiniteMarginal x L
  · rw [localMultiplicity, ite_eq_left hpos, Nat.cast_pow, Nat.cast_ofNat,
      LocalRunRank.infiniteMarginal_eq_squareClass_rank hL hpos]
    have hr := LocalRunRank.squareClass_rank_le x L hx
    have hidx : L = Module.finrank F₂ (squareClassSpace x L) + deficiency x L := by
      dsimp only [deficiency]
      omega
    conv_rhs => arg 1; rw [hidx, pow_add]
    field_simp
  · have hzero : infiniteMarginal x L = 0 := le_antisymm (le_of_not_gt hpos) hp
    rw [localMultiplicity, ite_eq_right hpos, Nat.cast_zero, mul_zero, hzero]

theorem mean_difference {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    countMoment G L 1 - (G.card : ℝ) * (2 ^ L : ℝ)⁻¹ = (2 ^ L : ℝ)⁻¹ * (bias G L : ℝ) := by
  calc
    _ = ∑ x ∈ G, (infiniteMarginal x L - (2 ^ L : ℝ)⁻¹) := by
      rw [countMoment_one hG, sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ = ∑ x ∈ G, (2 ^ L : ℝ)⁻¹ * ((localMultiplicity x L : ℝ) - 1) := by
      apply sum_congr rfl
      intro x hx
      have hxpos : 0 < x := by have h := (mem_Ico.mp (hG hx)).1; omega
      rw [nominal_times_multiplicity hxpos hL]
      ring
    _ = (2 ^ L : ℝ)⁻¹ * (bias G L : ℝ) := by
      simp only [bias, coefficient, Int.cast_sum, Int.cast_sub, Int.cast_natCast, Int.cast_one, mul_sum]

theorem main_17_3_integer_identity {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    countMoment (dyadicBlock N) L 1 - (N : ℝ) * (2 ^ L : ℝ)⁻¹ =
      (2 ^ L : ℝ)⁻¹ * (bias (dyadicBlock N) L : ℝ) := by
  simpa only [RegularSetFinite.card_dyadicBlock] using mean_difference hN hL (subset_refl (dyadicBlock N))

theorem mean_eq_nominal_iff_bias_zero {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    countMoment G L 1 = (G.card : ℝ) * (2 ^ L : ℝ)⁻¹ ↔ bias G L = 0 := by
  rw [← sub_eq_zero, mean_difference hN hL hG, mul_eq_zero]
  have hp : (2 ^ L : ℝ)⁻¹ ≠ 0 := by positivity
  simp only [hp, false_or, Int.cast_eq_zero]

theorem quantum_lower_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (hbias : bias G L ≠ 0) :
    (2 ^ L : ℝ)⁻¹ ≤ |countMoment G L 1 - (G.card : ℝ) * (2 ^ L : ℝ)⁻¹| := by
  have hquantum : (1 : ℝ) ≤ |(bias G L : ℝ)| := by exact_mod_cast Int.one_le_abs hbias
  rw [mean_difference hN hL hG, abs_mul, abs_of_pos (by positivity : 0 < (2 ^ L : ℝ)⁻¹)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hquantum (by positivity : 0 ≤ (2 ^ L : ℝ)⁻¹)

theorem finite_dichotomy {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    countMoment G L 1 = (G.card : ℝ) * (2 ^ L : ℝ)⁻¹ ∨
      (2 ^ L : ℝ)⁻¹ ≤ |countMoment G L 1 - (G.card : ℝ) * (2 ^ L : ℝ)⁻¹| := by
  by_cases hbias : bias G L = 0
  · exact Or.inl ((mean_eq_nominal_iff_bias_zero hN hL hG).mpr hbias)
  · exact Or.inr (quantum_lower_bound hN hL hG hbias)

theorem critical_quantum_lower_bound {N L : ℕ} {C : ℝ} (hN : 2 ≤ N) (hL : 0 < L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) (hbias : bias (dyadicBlock N) L ≠ 0) :
    ((2 : ℝ) ^ C)⁻¹ / N ≤ |countMoment (dyadicBlock N) L 1 - (N : ℝ) * (2 ^ L : ℝ)⁻¹| := by
  have h := (CriticalChannelPowers.nominal_lower hN hband).trans
    (quantum_lower_bound hN hL (subset_refl (dyadicBlock N)) hbias)
  simpa only [RegularSetFinite.card_dyadicBlock] using h

end PaperP1.MeanBiasQuantization
