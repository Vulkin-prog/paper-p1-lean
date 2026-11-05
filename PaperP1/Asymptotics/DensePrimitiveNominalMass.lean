module

public import PaperP1.Model.PrimitiveNominalMass
public import PaperP1.Asymptotics.PrimitiveGeneralMass
public import PaperP1.Asymptotics.DensePrimitiveHosts
public import Mathlib.Tactic.FieldSimp

/-! # Dense primitive homogeneous mass at fixed size r has exponent r-1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveNominalMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies
  PaperP1.PrimitiveNominalMass

theorem uniform_mass (r : ℕ) (hr : 3 ≤ r) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = r ∧ I ⊆ dyadicBlock N ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) →
        mass F L ≤ (N : ℝ) ^ (1 - (r : ℝ) + ε) := by
  classical
  obtain ⟨NC, _hNC, hNC⟩ := DensePrimitiveHosts.uniform_hosts r hr C η (ε / 2) hη (by positivity)
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ (r + 1))
    (1 - (r : ℝ) + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max NC NF), by omega, ?_⟩
  intro N hN L hband F hF
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hNC N (by omega) L hband F hF
  have hcap := LocalRigidityConsequences.nominal_marginal_bound hNtwo hband
  have hfactor := PrimitiveGeneralMass.binary_factor (by omega) hband
  have hdata : ∀ I ∈ F, I.card = r ∧ Primitive L I ∧ ∀ x ∈ I, 0 < x := by
    intro I hI
    refine ⟨(hF I hI).1, (hF I hI).2.2.1, ?_⟩
    intro x hx
    have hh := (mem_Ico.mp ((hF I hI).2.1 hx)).1
    omega
  have hproduct : (N : ℝ) ^ (ε / 2) *
      ((((2 : ℝ) ^ C / N) ^ r) * ((2 : ℝ) ^ C * N)) =
      ((2 : ℝ) ^ C) ^ (r + 1) * (N : ℝ) ^ (1 - (r : ℝ) + ε / 2) := by
    conv_rhs =>
      rw [show 1 - (r : ℝ) + ε / 2 = (ε / 2) + 1 - r by ring,
        Real.rpow_sub hn, Real.rpow_add hn, Real.rpow_one, Real.rpow_natCast]
    rw [div_pow, pow_succ]
    field_simp
  calc
    _ ≤ (F.card : ℝ) * (((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ L : ℝ)) :=
      primitive_mass_cap _ L r (by omega) hdata
    _ ≤ (N : ℝ) ^ (ε / 2) * (((2 ^ L : ℝ)⁻¹) ^ r * (2 ^ L : ℝ)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ (N : ℝ) ^ (ε / 2) *
        ((((2 : ℝ) ^ C / N) ^ r) * ((2 : ℝ) ^ C * N)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hcap r) hfactor (by positivity) (by positivity)
    _ = ((2 : ℝ) ^ C) ^ (r + 1) * (N : ℝ) ^ (1 - (r : ℝ) + ε / 2) := hproduct
    _ ≤ (N : ℝ) ^ (1 - (r : ℝ) + ε / 2 + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DensePrimitiveNominalMass
