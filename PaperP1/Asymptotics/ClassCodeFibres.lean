module

public import PaperP1.Arithmetic.CodedClassTargets
public import PaperP1.Asymptotics.DisjointSquareEquations
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Uniform counts for the actual two-class solution fibres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassCodeFibres

open Finset PaperP1.CodedClassTargets PaperP1.PhysicalClassData PaperP1.CriticalBandScale

theorem pair_count (s K : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ a b : Record s L, a.1.card ≤ K → b.1.card ≤ K → 0 < a.2 → 0 < b.2 →
        ((pairSolutions N a b).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NF, hNF⟩ := DisjointSquareEquations.two_equations 1 2 (by norm_num) K upperScale 1 ε hε
  obtain ⟨NG, hNG⟩ := critical_band_scale C
  refine ⟨max NF NG, ?_⟩
  intro N hN L hband a b ha hb hapos hbpos
  by_cases hgood : Good a.1 b.1
  · apply hNF N (by omega) (L + 1) (offsets a.1) (offsets b.1) (a.2 : ℤ) (b.2 : ℤ)
      (by omega) hgood.1 hgood.2.1 hgood.2.2
    · exact (offsets_card a.1).trans_le ((targets_card a.1).trans ha)
    · exact (offsets_card b.1).trans_le ((targets_card b.1).trans hb)
    · simpa only [Real.rpow_one] using (hNG N (by omega) L hband).2
    · intro u hu
      rcases mem_union.mp hu with hu | hu
      · exact offset_bound a.1 hu
      · exact offset_bound b.1 hu
    · exact_mod_cast hapos.ne'
    · exact_mod_cast hbpos.ne'
    · intro z hz
      obtain ⟨_, hz, hsqA, hsqB⟩ := (mem_pairSolutions a b).mp hz
      obtain ⟨hzlo, hzhi⟩ := mem_Ico.mp hz
      refine ⟨?_, ?_, hsqA, hsqB⟩
      · simpa only [one_mul] using (show (N : ℝ) ≤ z by exact_mod_cast hzlo)
      · exact_mod_cast hzhi.le
  · simp only [pairSolutions, hgood, ite_false, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) ε

end PaperP1.ClassCodeFibres
