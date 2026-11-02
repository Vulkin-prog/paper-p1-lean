module

public import PaperP1.Model.PrimitiveNominalMass
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import Mathlib.Tactic.FieldSimp

/-! # The nominal homogeneous primitive weight has the same elementary fixed-order exponent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveNominalCountMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveNominalMass

theorem uniform_mass (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
        mass (primitiveFamilies G L r) L ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NC, hNC⟩ := OriginalWindowFamilyCounts.uniform_hosts r hr C (ε / 2) (by positivity)
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ (r + 1))
    (1 - (r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NC NF), ?_⟩
  intro N hN L G hband hG
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := (hNC N (by omega) L G hband hG).2
  have hcap := LocalRigidityConsequences.nominal_marginal_bound hNtwo hband
  have hfactor := PrimitiveGeneralMass.binary_factor (by omega) hband
  have hF : ∀ I ∈ primitiveFamilies G L r, I.card = r ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x := by
    intro I hI
    obtain ⟨hI, hprim⟩ := mem_filter.mp hI
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hI
    refine ⟨hcard, hprim, ?_⟩
    intro x hx
    have hNx := (mem_Ico.mp (hG (hsub hx))).1
    omega
  have hproduct : (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) *
      ((((2 : ℝ) ^ C / N) ^ r) * ((2 : ℝ) ^ C * N)) =
      ((2 : ℝ) ^ C) ^ (r + 1) * (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2) := by
    conv_rhs =>
      rw [show 1 - (r : ℝ) / 2 + ε / 2 = ((r : ℝ) / 2 + ε / 2) + 1 - r by ring,
        Real.rpow_sub hn, Real.rpow_add hn, Real.rpow_one, Real.rpow_natCast]
    rw [div_pow, pow_succ]
    field_simp
  calc
    _ ≤ ((primitiveFamilies G L r).card : ℝ) * (((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ L : ℝ)) :=
      primitive_mass_cap _ L r (by omega) hF
    _ ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) * (((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ L : ℝ)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) *
        ((((2 : ℝ) ^ C / N) ^ r) * ((2 : ℝ) ^ C * N)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hcap r) hfactor (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ C) ^ (r + 1) * (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2) := hproduct
    _ ≤ (N : ℝ) ^ (1 - (r : ℝ) / 2 + ε / 2 + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrimitiveNominalCountMass
