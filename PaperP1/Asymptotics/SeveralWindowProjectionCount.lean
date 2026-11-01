module

public import PaperP1.Model.SeveralWindowProjections
public import PaperP1.Asymptotics.BlockSupportParameters
public import PaperP1.Arithmetic.OriginalWindowValueBounds
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Full companion T1.14 for actual original-window effective relations

The stronger exponent is r-s/2, for all injective centre tuples. The source
separated subclass inherits the printed weaker exponent.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralWindowProjectionCount

open Finset PaperP1.Model PaperP1.SeveralWindowProjections

theorem companion_T1_14 (r s : ℕ) (hs : 2 ≤ s) (Cband ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband → G ⊆ dyadicBlock N →
      ((tuples G L r s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) ∧
      ((tuples G L r s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - 2 * s / (2 * s + 1) + ε) := by
  classical
  obtain ⟨NC, hNC⟩ := PaperP1.BlockSupportCount.uniform_count r s 1 (by omega) (by norm_num)
    (1 / 2) 3 PaperP1.CriticalBandScale.upperScale ε (by norm_num) PaperP1.CriticalBandScale.upperScale_pos.le hε
  obtain ⟨NG, hNG⟩ := PaperP1.CriticalWindowGeometry.uniform_geometry Cband 0
  refine ⟨max NC NG, ?_⟩
  intro N hN L G hband hG
  obtain ⟨hNtwo, _, _, hthin, _, hBhi⟩ := hNG N (by omega) L hband
  have hL : L ≤ N := by omega
  have hcard : G.card ≤ 1 * N := (card_le_card hG).trans_eq (by
    simp only [dyadicBlock, Nat.card_Ico, one_mul]
    omega)
  have hdata : ∀ x ∈ G, ∀ v ∈ PaperP1.NormalizedWindowSets.values x L,
      ((1 / 2 : ℝ) * N ≤ v ∧ (v : ℝ) ≤ 3 * N) ∧ ((v : ℤ) - x).natAbs ≤ L + 1 := by
    intro x hx
    exact PaperP1.OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp (hG hx)) hL
  have hstrong : ((tuples G L r s).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) - (s : ℝ) / 2 + ε) := by
    rw [tuples_eq]
    exact hNC N (by omega) G (PaperP1.ConnectedWindowFamilies.blocks L r) hcard
      (fun _ x hx v hv ↦ (hdata x hx v hv).1)
      (fun _ x hx v hv ↦ (show (((v : ℤ) - x).natAbs : ℝ) ≤ (L + 1 : ℕ) by
        exact_mod_cast (hdata x hx v hv).2).trans hBhi)
  refine ⟨hstrong, hstrong.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    (by have h := PaperP1.BlockSupportCount.source_exponent r s hs; linarith only [h])

end PaperP1.SeveralWindowProjectionCount
