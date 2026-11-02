module

public import PaperP1.Arithmetic.ChannelSumIdentity
public import PaperP1.Arithmetic.ActualSourceTranslations
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # The literal finite-height explicit coefficients of the manuscript

An index is (height b, numerator a). The finite signed channel polynomials
and the factor two for the orientations are exactly the manuscript ones.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteChannelHierarchy

open Finset PaperP1.ChannelSumIdentity

def numerators (b : ℕ) : Finset ℕ :=
  (Icc 1 (b - 1)).filter fun a ↦ b < 2 * a ∧ a.Coprime b

def channels (h : ℕ) : Finset (Σ _b : ℕ, ℕ) :=
  (Icc 3 h).sigma numerators

def weight (a b : ℕ) : ℝ := (ActualSourceTranslations.coefficient a b : ℝ)

def heightSum (b L : ℕ) : ℝ :=
  ∑ a ∈ numerators b, weight a b * (signed L a b : ℝ)

def truncatedSum (h L : ℕ) : ℝ := ∑ b ∈ Icc 3 h, heightSum b L

def nominalMean (N L : ℕ) : ℝ := (N : ℝ) * (2 ^ L : ℝ)⁻¹

def coefficient (N L h : ℕ) : ℝ := (nominalMean N L) ^ 2 / N * truncatedSum h L

def twoChannelCoefficient (N L : ℕ) : ℝ :=
  (nominalMean N L) ^ 2 / (3 * N) * ((signed L 2 3 : ℝ) + (signed L 3 4 : ℝ))

theorem weight_formula (a b : ℕ) :
    weight a b = 2 * (2 * (a : ℝ) - b) / ((a : ℝ) * b) := by
  unfold weight ActualSourceTranslations.coefficient
  push_cast
  rfl

theorem mem_channels {h : ℕ} {z : Σ _b : ℕ, ℕ} :
    z ∈ channels h ↔ 3 ≤ z.1 ∧ z.1 ≤ h ∧ 1 ≤ z.2 ∧ z.2 < z.1 ∧
      z.1 < 2 * z.2 ∧ z.2.Coprime z.1 := by
  simp only [channels, mem_sigma, mem_Icc, numerators, mem_filter]
  constructor
  · rintro ⟨⟨hb, hbh⟩, ⟨ha, hab⟩, hba, hcop⟩
    exact ⟨hb, hbh, ha, by omega, hba, hcop⟩
  · rintro ⟨hb, hbh, ha, hab, hba, hcop⟩
    exact ⟨⟨hb, hbh⟩, ⟨ha, by omega⟩, hba, hcop⟩

theorem truncatedSum_eq_channels (h L : ℕ) :
    truncatedSum h L = ∑ z ∈ channels h, weight z.2 z.1 * (signed L z.2 z.1 : ℝ) := by
  unfold truncatedSum heightSum channels
  rw [sum_sigma]

theorem leading_channel_mem {h : ℕ} (hh : 3 ≤ h) :
    (⟨3, 2⟩ : Σ _b : ℕ, ℕ) ∈ channels h :=
  mem_channels.mpr ⟨by decide, hh, by decide, by decide, by decide, by decide⟩

theorem channels_three : channels 3 = {⟨3, 2⟩} := by decide

theorem channels_four : channels 4 = {⟨3, 2⟩, ⟨4, 3⟩} := by decide

theorem truncatedSum_three (L : ℕ) : truncatedSum 3 L = (1 / 3 : ℝ) * (signed L 2 3 : ℝ) := by
  rw [truncatedSum_eq_channels, channels_three, sum_singleton]
  norm_num [weight_formula]

theorem truncatedSum_four (L : ℕ) :
    truncatedSum 4 L = (1 / 3 : ℝ) * ((signed L 2 3 : ℝ) + (signed L 3 4 : ℝ)) := by
  rw [truncatedSum_eq_channels, channels_four, sum_pair (by decide)]
  norm_num [weight_formula]
  ring

theorem coefficient_four (N L : ℕ) (hN : 0 < N) : coefficient N L 4 = twoChannelCoefficient N L := by
  rw [coefficient, truncatedSum_four, twoChannelCoefficient]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end PaperP1.FiniteChannelHierarchy
