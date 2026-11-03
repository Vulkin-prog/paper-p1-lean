module

public import PaperP1.Asymptotics.DensePrimitiveFourMassUnderInputs
public import PaperP1.Asymptotics.PrimitiveFourLowMass

/-! # Complete main Proposition 15.5, with the dense exponent on the whole fixed-order population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveSharpMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass PaperP1.ConnectedWindowFamilies
  PaperP1.DensePrimitiveTripleMassUnderInputs

theorem uniform_four (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 4 ∧ Primitive L I) →
      mass F L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨p, hp⟩ := DensePrimitiveFourMassUnderInputs.uniform_bound C (1 / 2) (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := PrimitiveFourLowMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-(4 : ℝ) / 3 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo
  refine ⟨10 + NL + NA + ND, by omega, ?_⟩
  intro N hN L hband F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I : Finset ℕ ↦ (1 / 2 : ℝ) * L ≤ (runRelativeNullity L I : ℝ)
  let FD := F.filter P
  let FL := F.filter fun I ↦ ¬ P I
  have hdense : mass FD L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := hd N (by omega) L hband FD (by
    intro I hI
    obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
    exact ⟨(hF I hIF).1, (hF I hIF).2.1, (hF I hIF).2.2, hdim⟩)
  have hlow : mass FL L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
    apply (hl N (by omega) L hband FL ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    · intro I hI
      obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, (hF I hIF).2.1, (hF I hIF).2.2, lt_of_not_ge hdim⟩
  calc
    _ = mass FD L + mass FL L := (sum_filter_add_sum_filter_not F P (weight L)).symm
    _ ≤ 2 * (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by linarith only [hdense, hlow]
    _ ≤ (N : ℝ) ^ ((-(4 : ℝ) / 3 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

/-- The stronger source exponent holds for all primitive families, without a density premise. -/
theorem article_15_5 (r : ℕ) (hr : 4 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ F : Finset (Finset ℕ), F ⊆ primitiveFamilies G L r →
      mass F L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε) ∧
      mass F L ≤ (N : ℝ) ^ (-(2 * (r : ℝ)) / (r + 2) + ε) := by
  classical
  obtain ⟨p, hp⟩ := uniform_four C ε hε
  refine ⟨p, ?_⟩
  intro hgeo
  by_cases hr4 : r = 4
  · subst r
    obtain ⟨N₀, hN₀, h⟩ := hp hgeo
    refine ⟨N₀, hN₀, ?_⟩
    intro N hN L hband G hG F hF
    have hm := h N hN L hband F (by
      intro I hI
      obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp (hF hI)).1
      exact ⟨hIG.trans hG, hcard, (mem_filter.mp (hF hI)).2⟩)
    exact ⟨hm, by norm_num only [Nat.cast_ofNat] at *; exact hm⟩
  · obtain ⟨N₀, h⟩ := PrimitiveGeneralMass.main_15_5_from_five r (by omega) C ε hε
    refine ⟨max 10 N₀, by omega, ?_⟩
    intro N hN L hband G hG F hF
    exact h N (by omega) L G F hband hG hF

end PaperP1.PrimitiveSharpMassUnderInputs
