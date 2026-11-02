module

public import PaperP1.Arithmetic.FiniteChannelHierarchy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # The literal positive moving-phase constants and their first four heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelPhaseConstants

open Finset PaperP1.FiniteChannelHierarchy

def phaseSum (b : ℕ) : ℝ :=
  ∑ a ∈ numerators b, (2 * (a : ℝ) - b) * ((b : ℝ) - a) / a

def phaseConstant (b r : ℕ) : ℝ :=
  ((b : ℝ) + r - 1) / ((b : ℝ) ^ 2 * (2 : ℝ) ^ ((r : ℝ) / b)) * phaseSum b

theorem last_numerator (b : ℕ) (hb : 3 ≤ b) : b - 1 ∈ numerators b := by
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, le_rfl⟩, by omega, ?_⟩
  exact (Nat.coprime_self_sub_left (by omega : 1 ≤ b)).mpr (by simp)

theorem phaseTerm_pos {b a : ℕ} (ha : a ∈ numerators b) :
    0 < (2 * (a : ℝ) - b) * ((b : ℝ) - a) / a := by
  obtain ⟨ha, hba, _⟩ := mem_filter.mp ha
  obtain ⟨ha1, hab⟩ := mem_Icc.mp ha
  have hab' : a < b := by omega
  have haR : (0 : ℝ) < a := by exact_mod_cast ha1
  have habR : (a : ℝ) < b := by exact_mod_cast hab'
  have hbaR : (b : ℝ) < 2 * (a : ℝ) := by exact_mod_cast hba
  exact div_pos (mul_pos (sub_pos.mpr hbaR) (sub_pos.mpr habR)) haR

theorem phaseSum_pos (b : ℕ) (hb : 3 ≤ b) : 0 < phaseSum b := by
  have hmem := last_numerator b hb
  exact (phaseTerm_pos hmem).trans_le
    (single_le_sum (fun a ha ↦ (phaseTerm_pos ha).le) hmem)

theorem phaseConstant_pos (b r : ℕ) (hb : 3 ≤ b) : 0 < phaseConstant b r := by
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hnum : 0 < (b : ℝ) + r - 1 := by linarith [Nat.cast_nonneg (α := ℝ) r]
  unfold phaseConstant
  exact mul_pos (div_pos hnum (by positivity)) (phaseSum_pos b hb)

theorem numerators_three : numerators 3 = {2} := by decide

theorem numerators_four : numerators 4 = {3} := by decide

theorem numerators_five : numerators 5 = {3, 4} := by decide

theorem numerators_six : numerators 6 = {5} := by decide

theorem phaseSum_three : phaseSum 3 = 1 / 2 := by norm_num [phaseSum, numerators_three]

theorem phaseSum_four : phaseSum 4 = 2 / 3 := by norm_num [phaseSum, numerators_four]

theorem phaseSum_five : phaseSum 5 = 17 / 12 := by norm_num [phaseSum, numerators_five]

theorem phaseSum_six : phaseSum 6 = 4 / 5 := by norm_num [phaseSum, numerators_six]

theorem phaseConstant_three (r : ℕ) :
    phaseConstant 3 r = ((r : ℝ) + 2) / (18 * (2 : ℝ) ^ ((r : ℝ) / 3)) := by
  rw [phaseConstant, phaseSum_three]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

theorem phaseConstant_four (r : ℕ) :
    phaseConstant 4 r = ((r : ℝ) + 3) / (24 * (2 : ℝ) ^ ((r : ℝ) / 4)) := by
  rw [phaseConstant, phaseSum_four]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

theorem phaseConstant_five (r : ℕ) :
    phaseConstant 5 r = 17 * ((r : ℝ) + 4) / (300 * (2 : ℝ) ^ ((r : ℝ) / 5)) := by
  rw [phaseConstant, phaseSum_five]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

theorem phaseConstant_six (r : ℕ) :
    phaseConstant 6 r = ((r : ℝ) + 5) / (45 * (2 : ℝ) ^ ((r : ℝ) / 6)) := by
  rw [phaseConstant, phaseSum_six]
  norm_num only [Nat.cast_ofNat]
  field_simp
  ring

end PaperP1.ChannelPhaseConstants
