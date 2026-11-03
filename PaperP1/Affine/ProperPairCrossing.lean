module

public import PaperP1.Affine.MinimalSpanCrossing

/-! # Directness from each target suffices for every proper subset of two targets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProperPairCrossing

open Finset PaperP1.SubspaceFamilyRank

theorem proper_direct {ι : Type*} [DecidableEq ι] {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (S : ι → Submodule K V) (W : Submodule K V) (y z : ι)
    (hy : Disjoint W (S y)) (hz : Disjoint W (S z)) :
    ∀ B : Finset ι, B ⊂ {y, z} → Disjoint W (span S B) := by
  classical
  intro B hB
  have hcard : B.card ≤ 1 := by
    have hlt := card_lt_card hB
    have hle : ({y, z} : Finset ι).card ≤ 2 := card_le_two
    omega
  by_cases hempty : B = ∅
  · simp [hempty, span_empty]
  · obtain ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr hempty
    have heq : B = {b} := eq_of_subset_of_card_le (singleton_subset_iff.mpr hb) (by simpa using hcard) |>.symm
    have hbmem := hB.1 hb
    have hs : span S {b} = S b := by simp [span]
    rw [heq, hs]
    rcases mem_insert.mp hbmem with hby | hbz
    · exact hby ▸ hy
    · exact (mem_singleton.mp hbz) ▸ hz

end PaperP1.ProperPairCrossing
