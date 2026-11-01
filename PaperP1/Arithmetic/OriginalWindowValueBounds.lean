module

public import PaperP1.Arithmetic.NormalizedWindowSets
public import Mathlib.Basic.Real.Basic

/-! # Literal height and signed-distance bounds for complete original windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalWindowValueBounds

open Finset

theorem values_geometry (N L x : ℕ) (hN : 2 ≤ N) (hx : N ≤ x ∧ x < 2 * N) (hL : L ≤ N) :
    ∀ v ∈ PaperP1.NormalizedWindowSets.values x L,
      ((1 / 2 : ℝ) * N ≤ v ∧ (v : ℝ) ≤ 3 * N) ∧ ((v : ℤ) - x).natAbs ≤ L + 1 := by
  intro v hv
  rw [PaperP1.NormalizedWindowSets.values_eq_interval (by omega : 0 < x)] at hv
  obtain ⟨hvlo, hvhi⟩ := mem_Ico.mp hv
  have hloNat : N ≤ 2 * v := by omega
  have hhiNat : v ≤ 3 * N := by omega
  have hloReal : (N : ℝ) ≤ 2 * v := by exact_mod_cast hloNat
  have hhiReal : (v : ℝ) ≤ 3 * N := by exact_mod_cast hhiNat
  refine ⟨⟨by linarith only [hloReal], hhiReal⟩, ?_⟩
  have hdown : x ≤ v + (L + 1) := by omega
  have hup : v ≤ x + (L + 1) := by omega
  have hdownZ : (x : ℤ) ≤ v + (L + 1 : ℕ) := by exact_mod_cast hdown
  have hupZ : (v : ℤ) ≤ x + (L + 1 : ℕ) := by exact_mod_cast hup
  have habs : |(v : ℤ) - x| ≤ (L + 1 : ℕ) := abs_le.mpr ⟨by omega, by omega⟩
  rw [Int.abs_eq_natAbs] at habs
  exact_mod_cast habs

end PaperP1.OriginalWindowValueBounds
