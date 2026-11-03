module

public import PaperP1.Combinatorics.TwoTargetFamilyCover

/-! # Triples covered by a source vertex satisfying an actual source-specific predicate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RestrictedSingletonPairCover

open Finset

def fibers (F : Finset (Finset ℕ)) (R : ℕ → Finset ℕ → Prop) (x : ℕ) : Finset (Finset ℕ) := by
  classical
  exact F.filter fun T ↦ x ∈ T ∧ R x T

theorem mem_fibers (F : Finset (Finset ℕ)) (R : ℕ → Finset ℕ → Prop) (x : ℕ) (T : Finset ℕ) :
    T ∈ fibers F R x ↔ T ∈ F ∧ x ∈ T ∧ R x T := by
  classical
  exact mem_filter

theorem weighted_cover (G : Finset ℕ) (F : Finset (Finset ℕ))
    (R : ℕ → Finset ℕ → Prop) (w : Finset ℕ → ℝ) (hw : ∀ T, 0 ≤ w T)
    (hF : ∀ T ∈ F, T ⊆ G ∧ T.card = 3)
    (hcover : ∀ T ∈ F, ∃ x ∈ T, R x T) :
    (∑ T ∈ F, w T) ≤ ∑ x ∈ G,
      ∑ p ∈ TwoTargetFamilyCover.pairs G {x} (fibers F R x),
        w (TwoTargetFamilyCover.family {x} p) := by
  classical
  have hsub : F ⊆ G.biUnion (fibers F R) := by
    intro T hT
    obtain ⟨x, hx, hR⟩ := hcover T hT
    exact mem_biUnion.mpr ⟨x, (hF T hT).1 hx, mem_filter.mpr ⟨hT, hx, hR⟩⟩
  calc
    _ ≤ ∑ T ∈ G.biUnion (fibers F R), w T :=
      sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ ↦ hw T)
    _ ≤ ∑ x ∈ G, ∑ T ∈ fibers F R x, w T :=
      GraphStarWeights.sum_biUnion_le_nonneg G (fibers F R) w hw
    _ ≤ _ := by
      apply sum_le_sum
      intro x _hx
      apply TwoTargetFamilyCover.extension_sum_le G {x} (fibers F R x) w hw
      intro T hT
      obtain ⟨hTF, hxT, _hR⟩ := mem_filter.mp hT
      exact ⟨(hF T hTF).1, singleton_subset_iff.mpr hxT, by simpa using (hF T hTF).2⟩

theorem erase_source (x : ℕ) (p : ℕ × ℕ) (hx : p.1 ≠ x) (hy : p.2 ≠ x) :
    (TwoTargetFamilyCover.family {x} p).erase x = {p.1, p.2} := by
  classical
  ext z
  simp only [mem_erase, TwoTargetFamilyCover.family, mem_insert, mem_singleton]
  aesop

end PaperP1.RestrictedSingletonPairCover
