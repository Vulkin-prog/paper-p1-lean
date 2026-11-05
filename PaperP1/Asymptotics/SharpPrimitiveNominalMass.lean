module

public import PaperP1.Asymptotics.DensePrimitiveNominalMass
public import PaperP1.Asymptotics.LowPrimitiveNominalMass

/-! # All primitive families of fixed size r have homogeneous mass of power r/2

Both low-nullity counting and dense confinement are internally proved. Zero marginals and incompatible affine systems are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpPrimitiveNominalMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.PrimitiveNominalMass

theorem uniform_mass
    (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = r ∧ Primitive L I) →
        mass F L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨b, hb⟩ := exists_nat_gt (max 1 (4 / ε))
  have hbR : (0 : ℝ) < b := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hb)
  have hbN : 0 < b := by exact_mod_cast hbR
  have hprod : 4 < (b : ℝ) * ε := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hb)
  have hsmall : 1 / (b : ℝ) ≤ ε / 4 := (div_le_iff₀ hbR).mpr (by nlinarith only [hprod])
  obtain ⟨ND, _hND, hd⟩ := DensePrimitiveNominalMass.uniform_mass
    r hr C (1 / (b : ℝ)) (ε / 2) (by positivity) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := LowPrimitiveNominalMass.uniform_bound r hr b hbN C (ε / 4) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-(r : ℝ) / 2 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨3 + ND + NL + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I ↦ (1 / (b : ℝ)) * L ≤ (runRelativeNullity L I : ℝ)
  let FD := F.filter P
  let FL := F.filter fun I ↦ ¬P I
  have hdense : mass FD L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) := by
    have hh := hd N (by omega) L hband FD (by
      intro I hI
      obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
      obtain ⟨hdyadic, hcard, hprim⟩ := hF I hIF
      exact ⟨hcard, hdyadic, hprim, hdim⟩)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by
      have hrr : (3 : ℝ) ≤ r := by exact_mod_cast hr
      linarith))
  have hlow : mass FL L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) := by
    have hh := hl N (by omega) L hband FL (by
      intro I hI
      obtain ⟨hIF, hdim⟩ := mem_filter.mp hI
      obtain ⟨hdyadic, hcard, hprim⟩ := hF I hIF
      refine ⟨hdyadic, hcard, hprim, ?_⟩
      have hlt : (runRelativeNullity L I : ℝ) < (1 / (b : ℝ)) * L := lt_of_not_ge hdim
      have he : (1 / (b : ℝ)) * L = (L : ℝ) / b := by ring
      exact he ▸ hlt)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hsmall]))
  calc
    _ = mass FD L + mass FL L := (sum_filter_add_sum_filter_not F P (weight L)).symm
    _ ≤ 2 * (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) := by linarith only [hdense, hlow]
    _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

/-- Both original exponents hold on the entire primitive population, without density. -/
theorem article_15_5 (r : ℕ) (hr : 4 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ F : Finset (Finset ℕ), F ⊆ primitiveFamilies G L r →
      mass F L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε) ∧
      mass F L ≤ (N : ℝ) ^ (-(2 * (r : ℝ)) / (r + 2) + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass r (by omega) C ε hε
  refine ⟨max 10 NM, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hh := hm N (by omega) L hband F (by
    intro I hI
    obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp (mem_filter.mp (hF hI)).1
    exact ⟨hIG.trans hG, hcard, (mem_filter.mp (hF hI)).2⟩)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  constructor
  · exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  · apply hh.trans
    apply Real.rpow_le_rpow_of_exponent_le hn
    suffices -(r : ℝ) / 2 ≤ -(2 * (r : ℝ)) / (r + 2) by linarith
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 2)).mpr
    nlinarith only [mul_nonneg (show 0 ≤ (r : ℝ) - 2 by linarith) (Nat.cast_nonneg r)]

end PaperP1.SharpPrimitiveNominalMass
