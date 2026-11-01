module

public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Arithmetic.OriginalWindowValueBounds
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.RelativeBlockRelationsCount

/-! # Actual unordered connected and primitive original-window host counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalWindowFamilyCounts

open Finset PaperP1.ConnectedWindowFamilies PaperP1.Model

theorem uniform_hosts (r : ℕ) (hr : 2 ≤ r) (Cband ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → G ⊆ dyadicBlock N →
      ((connectedFamilies G L r).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) ∧
      ((primitiveFamilies G L r).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NC, hNC⟩ := PaperP1.RelativeBlockRelationsCount.uniform_count r 0 (1 / 2) 3
    PaperP1.CriticalBandScale.upperScale ε (by norm_num) PaperP1.CriticalBandScale.upperScale_pos.le hε
  obtain ⟨NG, hNG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry Cband 0
  refine ⟨max NC NG, ?_⟩
  intro N hN L G hband hG
  obtain ⟨hNtwo, _, _, hthin, _, hBhi⟩ := hNG N (by omega) L hband
  have hL : L ≤ N := by omega
  have hdata : ∀ x ∈ G, ∀ v ∈ PaperP1.NormalizedWindowSets.values x L,
      ((1 / 2 : ℝ) * N ≤ v ∧ (v : ℝ) ≤ 3 * N) ∧ ((v : ℤ) - x).natAbs ≤ L + 1 := by
    intro x hx
    exact PaperP1.OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp (hG hx)) hL
  let old : Fin 0 → ℕ := Fin.elim0
  let oldBlocks : Fin 0 → Finset ℕ := Fin.elim0
  have hcount : ((PaperP1.RelativeBlockRelations.population G (blocks L r) ∅).card : ℝ) ≤
      (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
    have hc := hNC N (by omega) old oldBlocks G (blocks L r)
      (fun _ x hx v hv ↦ (hdata x hx v hv).1) (fun k ↦ Fin.elim0 k)
      (fun _ x hx v hv ↦ (show (((v : ℤ) - x).natAbs : ℝ) ≤ (L + 1 : ℕ) by
        exact_mod_cast (hdata x hx v hv).2).trans hBhi) (fun k ↦ Fin.elim0 k)
    simpa using hc
  exact ⟨(show ((connectedFamilies G L r).card : ℝ) ≤
      (PaperP1.RelativeBlockRelations.population G (blocks L r) ∅).card by
        exact_mod_cast connected_family_count G L r hr).trans hcount,
    (show ((primitiveFamilies G L r).card : ℝ) ≤
      (PaperP1.RelativeBlockRelations.population G (blocks L r) ∅).card by
        exact_mod_cast primitive_family_count G L r).trans hcount⟩

end PaperP1.OriginalWindowFamilyCounts
