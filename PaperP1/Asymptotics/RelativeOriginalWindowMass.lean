module

public import PaperP1.Model.RelativeWindowFamilies
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Actual unordered target families participating above arbitrary prescribed effective sources have uniform half-power independent mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeOriginalWindowMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FamilyIndependentMass PaperP1.RelativeWindowFamilies PaperP1.CriticalBandScale

theorem uniform_mass (r s : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ old : Fin s → ℕ, (∀ i, old i ∈ dyadicBlock N) →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ⨆ i, squareClassSpace (old i) L →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ((RelativeWindowFamilies.families G L r W).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) ∧
        independentMass (RelativeWindowFamilies.families G L r W) L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
  classical
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let M := 2 * (2 : ℝ) ^ C
  obtain ⟨Nr, hr⟩ := RelativeBlockRelationsCount.uniform_count r s (1 / 2) 3 upperScale δ
    (by norm_num) upperScale_pos.le hδ
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨Nm, _hNm, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨Na, ha⟩ := HalfCountSchedule.factor_absorption (M ^ r) (-(r : ℝ) / 2 + δ) δ hδ
  refine ⟨max 3 (max Nr (max Ng (max Nm Na))), by omega, ?_⟩
  intro N hN L hband old hold W hW G hG
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgeom := hg N (by omega) L hband
  have hLN : L ≤ N := by have h := hgeom.2.2.2.1; omega
  have hwidth := hgeom.2.2.2.2.2
  have hdata (x : ℕ) (hx : x ∈ dyadicBlock N) := OriginalWindowValueBounds.values_geometry N L x
    (by omega) (mem_Ico.mp hx) hLN
  let oldBlocks := fun i : Fin s ↦ NormalizedWindowSets.values (old i) L
  let O := univ.biUnion oldBlocks
  have hcount := hr N (by omega) old oldBlocks G (ConnectedWindowFamilies.blocks L r)
    (fun _ x hx v hv ↦ (hdata x (hG hx) v hv).1)
    (fun i v hv ↦ (hdata (old i) (hold i) v hv).1)
    (fun _ x hx v hv ↦ (show (((v : ℤ) - x).natAbs : ℝ) ≤ (L + 1 : ℕ) by
      exact_mod_cast (hdata x (hG hx) v hv).2).trans hwidth)
    (fun i v hv ↦ (show (((v : ℤ) - old i).natAbs : ℝ) ≤ (L + 1 : ℕ) by
      exact_mod_cast (hdata (old i) (hold i) v hv).2).trans hwidth)
  have hfamily : ((RelativeWindowFamilies.families G L r W).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + δ) :=
    (show ((RelativeWindowFamilies.families G L r W).card : ℝ) ≤
      (RelativeBlockRelations.population G (ConnectedWindowFamilies.blocks L r) O).card by
        exact_mod_cast RelativeWindowFamilies.family_count G L r W O (old_space_bound old L W hW)).trans hcount
  have hfinite := finite_mass_cap (RelativeWindowFamilies.families G L r W) G L r (M / N) (by
    intro I hI
    exact mem_powersetCard.mp (mem_filter.mp hI).1)
    (fun x hx ↦ hm N (by omega) L hband x (hG hx))
  have hmass : independentMass (RelativeWindowFamilies.families G L r W) L ≤
      (N : ℝ) ^ (-(r : ℝ) / 2 + ε) := by
    calc
      _ ≤ (N : ℝ) ^ ((r : ℝ) / 2 + δ) * (M / N) ^ r :=
        hfinite.trans (mul_le_mul_of_nonneg_right hfamily (by dsimp [M]; positivity))
      _ = M ^ r * ((N : ℝ) ^ ((r : ℝ) / 2 + δ) / (N : ℝ) ^ r) := by rw [div_pow]; ring
      _ = M ^ r * (N : ℝ) ^ (((r : ℝ) / 2 + δ) - r) := by rw [Real.rpow_sub hNr, Real.rpow_natCast]
      _ = M ^ r * (N : ℝ) ^ (-(r : ℝ) / 2 + δ) := by congr 2; ring
      _ ≤ (N : ℝ) ^ ((-(r : ℝ) / 2 + δ) + δ) := ha N (by omega)
      _ = _ := by congr 1; dsimp [δ]; ring
  exact ⟨hfamily.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [δ]; linarith only [hε])), hmass⟩

end PaperP1.RelativeOriginalWindowMass
