module

public import PaperP1.Asymptotics.ActiveBlockCentresCount
public import PaperP1.Asymptotics.ValueHeightHalfCount

/-! # Main 10.3: actual dependent block pairs, including the diagonal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DependentBlockPairsCount

open Finset PaperP1.DependentBlockPairs

theorem article_10_3 (a b D Cband ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ blocks : Fin 2 → ℕ → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x,
        (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      ((pairs G blocks).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  classical
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NO, hNO⟩ := PaperP1.ValueHeightHalfCount.article_10_1 2 0 a b D Cband η ha hD hη
  obtain ⟨ND, hND⟩ := PaperP1.ActiveBlockCentresCount.uniform_count a b D Cband η ha hD hη
  obtain ⟨NF, hNF⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (1 + η) η hη
  refine ⟨max NO (max ND NF), ?_⟩
  intro N hN L G blocks hband hvalues hdist
  let old : Fin 0 → ℕ := Fin.elim0
  let oldBlocks : Fin 0 → Finset ℕ := Fin.elim0
  have hactual : ((PaperP1.EffectiveWindowLists.lists G blocks ∅).card : ℝ) ≤ (N : ℝ) ^ (1 + η) := by
    simpa using hNO N (by omega) L old G blocks oldBlocks hband hvalues
      (fun k ↦ Fin.elim0 k) hdist (fun k ↦ Fin.elim0 k)
  have hoff : ((offDiagonal G blocks).card : ℝ) ≤ (N : ℝ) ^ (1 + η) :=
    (show ((offDiagonal G blocks).card : ℝ) ≤ (PaperP1.EffectiveWindowLists.lists G blocks ∅).card by
      exact_mod_cast off_diagonal_count G blocks).trans hactual
  have hdiag : ((diagonal G blocks).card : ℝ) ≤ (N : ℝ) ^ (1 + η) :=
    (show ((diagonal G blocks).card : ℝ) ≤ (active G (blocks 0)).card by
      exact_mod_cast diagonal_count G blocks).trans
    (hND N (by omega) L G (blocks 0) hband (hvalues 0) (hdist 0))
  have hsplit : ((pairs G blocks).card : ℝ) ≤ ((offDiagonal G blocks).card : ℝ) +
      ((diagonal G blocks).card : ℝ) := by exact_mod_cast split_count G blocks
  calc
    _ ≤ 2 * (N : ℝ) ^ (1 + η) := by linarith only [hsplit, hoff, hdiag]
    _ ≤ (N : ℝ) ^ ((1 + η) + η) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem uniform_logarithmic_count (a b E ε : ℝ) (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : Finset ℕ, ∀ blocks : Fin 2 → ℕ → Finset ℕ,
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x,
        (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
      ((pairs G blocks).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NI, hNI⟩ := article_10_3 a b (E / PaperP1.CriticalBandScale.lowerScale) 1 ε
    ha (div_nonneg hE PaperP1.CriticalBandScale.lowerScale_pos.le) hε
  obtain ⟨NT, hNT⟩ := PaperP1.LogarithmicBlockGeometry.width_transfer E hE
  refine ⟨max NI NT, ?_⟩
  intro N hN G blocks hvalues hdist
  have htransfer := hNT N (by omega)
  exact hNI N (by omega) (PaperP1.LogarithmicBlockGeometry.length N) G blocks htransfer.1
    hvalues (fun i x hx v hv ↦ (hdist i x hx v hv).trans htransfer.2)

end PaperP1.DependentBlockPairsCount
