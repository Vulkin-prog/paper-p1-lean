module

public import PaperP1.Asymptotics.ConditionalHalfCount
public import PaperP1.Arithmetic.EffectiveWindowLists

/-! # The conditional half-count for arbitrary finite effective blocks

The old space is the full value span, and every new projection is nonzero
in its own absolute even-selection image. Old blocks may overlap or depend.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EffectiveHalfCount

open Finset PaperP1.ProjectedWindowLists PaperP1.EffectiveWindowLists

theorem old_blocks_subset {s : ℕ} (W : ℕ) (old : Fin s → ℕ) (O : Fin s → Finset ℕ)
    (hO : ∀ k, O k ⊆ blockValues W (old k)) :
    univ.biUnion O ⊆ oldValues W old := by
  intro v hv
  obtain ⟨k, _, hvk⟩ := mem_biUnion.mp hv
  exact mem_biUnion.mpr ⟨k, mem_univ _, hO k hvk⟩

theorem uniform_effective_count (r s : ℕ) (a b E ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ old : Fin s → ℕ, ∀ G : Finset ℕ,
      ∀ blocks : Fin r → ℕ → Finset ℕ, ∀ O : Finset ℕ,
      0 < W → (W : ℝ) ≤ E * Real.log N →
      (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      (∀ k, a * N ≤ old k ∧ (old k : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, blocks i x ⊆ blockValues W x) → O ⊆ oldValues W old →
      ((PaperP1.EffectiveWindowLists.lists G blocks O).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NI, hNI⟩ := PaperP1.ConditionalHalfCount.uniform_count r s a b E ε ha hE hε
  obtain ⟨C, _, hcompare⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨NV, hNV⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre C E 1
  refine ⟨max NI NV, ?_⟩
  intro N hN W old G blocks O hW hwidth hG hold hblocks hO
  let T := G ∪ univ.image old
  have hT : ∀ x ∈ T, a * N ≤ x ∧ (x : ℝ) ≤ b * N := by
    intro x hx
    rcases mem_union.mp hx with hxG | hxold
    · exact hG x hxG
    · obtain ⟨k, _, rfl⟩ := mem_image.mp hxold
      exact hold k
  have holdT : ∀ k, old k ∈ T := fun k ↦ mem_union_right _ (mem_image.mpr ⟨k, mem_univ _, rfl⟩)
  have hGpos : ∀ x ∈ G, W < x := by
    intro x hx
    exact hNV N (by omega) x W (hcompare N x (hG x hx).1 (hG x hx).2).1
      (by simpa only [Real.rpow_one] using hwidth)
  have hsub := subset_window_lists G T W old blocks O subset_union_left hGpos hblocks hO
  exact (show ((PaperP1.EffectiveWindowLists.lists G blocks O).card : ℝ) ≤
    ((PaperP1.ProjectedWindowLists.lists (r := r) T W old).card : ℝ) by
      exact_mod_cast card_le_card hsub).trans
    (hNI N (by omega) W old T hW hwidth hT holdT)

theorem critical_centre_count (r s : ℕ) (a b D Cband ε : ℝ)
    (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ old : Fin s → ℕ, ∀ G : Finset ℕ,
      ∀ blocks : Fin r → ℕ → Finset ℕ, ∀ oldBlocks : Fin s → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (∀ x ∈ G, a * N ≤ x ∧ (x : ℝ) ≤ b * N) →
      (∀ k, a * N ≤ old k ∧ (old k : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x,
        (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      (∀ k, ∀ v ∈ oldBlocks k,
        (((v : ℤ) - old k).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      ((PaperP1.EffectiveWindowLists.lists G blocks (univ.biUnion oldBlocks)).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  let E := D * PaperP1.CriticalBandScale.upperScale + 2
  have hE : 0 ≤ E := by
    have := PaperP1.CriticalBandScale.upperScale_pos
    dsimp [E]
    positivity
  obtain ⟨NI, hNI⟩ := uniform_effective_count r s a b E ε ha hE hε
  obtain ⟨NB, hNB⟩ := PaperP1.CriticalBandScale.critical_band_scale Cband
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max NI (max NB NL), ?_⟩
  intro N hN L old G blocks oldBlocks hband hG hold hblocks holdBlocks
  let W := ⌈D * (L + 1 : ℕ)⌉₊ + 1
  have hlog : 1 ≤ Real.log N := hNL N (by omega)
  have hDB : D * (L + 1 : ℕ) ≤ (D * PaperP1.CriticalBandScale.upperScale) * Real.log N := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hNB N (by omega) L hband).2 hD
  have hceil : (⌈D * (L + 1 : ℕ)⌉₊ : ℝ) < D * (L + 1 : ℕ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hwidth : (W : ℝ) ≤ E * Real.log N := by
    dsimp [W, E]
    push_cast at hceil hDB ⊢
    nlinarith only [hceil, hDB, hlog]
  have hnew : ∀ i, ∀ x ∈ G, blocks i x ⊆ blockValues W x := by
    intro i x hx v hv
    apply mem_blockValues_of_distance
    have hcast : (((v : ℤ) - x).natAbs : ℝ) ≤ (⌈D * (L + 1 : ℕ)⌉₊ : ℝ) :=
      (hblocks i x hx v hv).trans (Nat.le_ceil _)
    have hnat : ((v : ℤ) - x).natAbs ≤ ⌈D * (L + 1 : ℕ)⌉₊ := by exact_mod_cast hcast
    dsimp [W]
    omega
  have holdsub : ∀ k, oldBlocks k ⊆ blockValues W (old k) := by
    intro k v hv
    apply mem_blockValues_of_distance
    have hcast : (((v : ℤ) - old k).natAbs : ℝ) ≤ (⌈D * (L + 1 : ℕ)⌉₊ : ℝ) :=
      (holdBlocks k v hv).trans (Nat.le_ceil _)
    have hnat : ((v : ℤ) - old k).natAbs ≤ ⌈D * (L + 1 : ℕ)⌉₊ := by exact_mod_cast hcast
    dsimp [W]
    omega
  exact hNI N (by omega) W old G blocks (univ.biUnion oldBlocks) (by dsimp [W]; omega)
    hwidth hG hold hnew (old_blocks_subset W old oldBlocks holdsub)

end PaperP1.EffectiveHalfCount
