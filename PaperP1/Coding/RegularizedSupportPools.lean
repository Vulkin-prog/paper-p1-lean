module

public import PaperP1.Combinatorics.BinaryLabelRepresentations
public import PaperP1.Combinatorics.PhysicalLabelSupportCount
public import PaperP1.Coding.DisjointRecoveryTheorem

/-! # Actual uniformly bounded support pools after disjoint-recovery regularization -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularizedSupportPools

open Finset PaperP1.Affine PaperP1.ZeroSumFreeRepresentations
  PaperP1.PhysicalLabelSupportCount PaperP1.DisjointRecoverySubspace
  PaperP1.DisjointRecoveryTheorem PaperP1.RecoveryLabelSupports

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
  [AddCommGroup W] [Module 𝔽₂ W]

theorem support_pool_contains (L : V → W) (S : Finset W) (d : ℕ) (A : Finset V)
    (hlabels : ∀ v ∈ A, L v ≠ 0 → L v ∈ S) (hcard : A.card ≤ d)
    (α : W) (hα : α ≠ 0) (hsum : (∑ v ∈ A, L v) = α) :
    ∃ D ⊆ A, D ∈ supportPool L S d α ∧ D.Nonempty ∧ D.card ≤ d ∧
      Set.InjOn L (D : Set V) ∧ (∑ v ∈ D, L v) = α := by
  obtain ⟨B, hBsub, hBne, hBfree, hBzero, hBcard, hsumB⟩ :=
    BinaryLabelRepresentations.physical_representation L A α hα hsum
  obtain ⟨D, hDsub, hDimage, hDcard, hDinj⟩ := injective_lift L A B hBsub
  have hBS : B ⊆ S := by
    intro b hb
    obtain ⟨v, hv, hvb⟩ := mem_image.mp (hBsub hb)
    rw [← hvb]
    apply hlabels v hv
    intro hz
    exact hBzero ((hvb.symm.trans hz) ▸ hb)
  have hBr : B ∈ representations S B.card α :=
    mem_representations.mpr ⟨hBS, rfl, hBfree, hsumB⟩
  have hDpool : D ∈ supportPool L S d α := by
    apply mem_biUnion.mpr
    refine ⟨B.card, mem_Icc.mpr ⟨by have h := hBne.card_pos; omega, hBcard.trans hcard⟩, ?_⟩
    apply mem_filter.mpr
    exact ⟨mem_powerset.mpr (subset_univ _), hDimage.symm ▸ hBr⟩
  refine ⟨D, hDsub, hDpool, card_pos.mp (by rw [hDcard]; exact hBne.card_pos),
    by rw [hDcard]; exact hBcard.trans hcard, hDinj, ?_⟩
  calc
    _ = ∑ b ∈ D.image L, b := by rw [sum_image hDinj]
    _ = α := by rw [hDimage]; exact hsumB

variable {U : Type*} [AddCommGroup U] [Module 𝔽₂ U] [FiniteDimensional 𝔽₂ U]

local instance regularizedSupportDualDecEq (M : Submodule 𝔽₂ U) : DecidableEq (Module.Dual 𝔽₂ M) :=
  Classical.decEq _

omit [DecidableEq W] [AddCommGroup W] [Module 𝔽₂ W] in
theorem regularized_pools (L : V → Module.Dual 𝔽₂ U) (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule 𝔽₂ U, RecoveryConclusion L M d t (t - 1) ∧
      ∀ α : Module.Dual 𝔽₂ M, α ≠ 0 →
        (supportPool (fun v ↦ (L v).comp M.subtype) (labels L M) d α).card ≤
          supportBound d t (t - 1) := by
  obtain ⟨M, hM⟩ := disjoint_recovery_sharp L d t hd ht
  have hno := noDisjointSums_of_recovery_exclusion L M d t (by omega) hM.2.1
  refine ⟨M, hM, ?_⟩
  intro α hα
  apply supportPool_card _ _ d t (t - 1) hno
  · intro a ha
    exact hM.2.2.1 a ((mem_labels L M a).mp ha).1
  · exact hα

end PaperP1.RegularizedSupportPools
