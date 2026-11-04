module

public import PaperP1.Asymptotics.BoundedBlockIndependentTail
public import PaperP1.Asymptotics.CompressedBlockIndependentTail

/-! # Both clauses of the independent full-support tail, with a common fixed cutoff

The arbitrary old block may have any actual finite label set contained in the
stated complete window. Thus a finite collection of geometric types is covered
by increasing the fixed range and width constants. The actual normalized source
blocks are also instantiated in CompressedBlockIndependentTail.uniform_channel.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentTailTheorem

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem original_mass_antitone (G : Finset ℕ) (L : ℕ) (v : ℝ) (hv : 0 ≤ v)
    {s t : ℕ} (hst : s ≤ t) :
    IndependentFullSupportTail.mass G L t v ≤ IndependentFullSupportTail.mass G L s v := by
  classical
  unfold IndependentFullSupportTail.mass
  apply sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨hIG, hsize, hfull⟩ := (IndependentFullSupportTail.mem_families G I L t).mp hI
    exact (IndependentFullSupportTail.mem_families G I L s).mpr ⟨hIG, hst.trans hsize, hfull⟩
  · intro I _ _
    exact prod_nonneg fun x _ ↦ mul_nonneg hv (MissingBlockProbabilities.infiniteMarginal_nonneg x L)

theorem article_15_8 (D Q : ℕ) (hD : 1 ≤ D) (hQ : 2 ≤ Q) (C v a ε : ℝ)
    (hv : 0 < v) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      IndependentFullSupportTail.mass (dyadicBlock N) L s v ≤ (N : ℝ) ^ (-a + ε) ∧
      (∀ U : ℕ → Finset ℕ,
        (∀ x ∈ Ico 2 (Q * N + 2), U x ⊆ NormalizedWindowSets.values x (D * (L + 1))) →
        BoundedBlockIndependentTail.mass Q N L (s - 1) v U ≤ (N : ℝ) ^ (-a + ε)) := by
  obtain ⟨s₀, _hs₀, NO, _hNO, ho⟩ := FullSupportIndependentTail.article_15_8_original C v a ε hv ha hε
  obtain ⟨s₁, hs₁, NB, _hNB, hb⟩ := BoundedBlockIndependentTail.uniform_blocks D Q hD hQ C v a ε hv ha hε
  refine ⟨max s₀ s₁ + 1, by omega, max 10 (max NO NB), by omega, ?_⟩
  intro N hN L hband
  refine ⟨?_, ?_⟩
  · exact (original_mass_antitone (dyadicBlock N) L v hv.le (by omega : s₀ ≤ max s₀ s₁ + 1)).trans
      (ho N (by omega) L hband (dyadicBlock N) (subset_refl _))
  · intro U hU
    exact (BoundedBlockIndependentTail.mass_antitone Q N L v hv.le U (by omega : s₁ ≤ max s₀ s₁ + 1 - 1)).trans
      (hb N (by omega) L hband U hU)

end PaperP1.IndependentTailTheorem
