module

public import PaperP1.Coding.RegularizedSupportPools
public import PaperP1.Affine.PairFourierIntersection

/-! # Bounded incidence of complete binary and ternary active prime supports

With at most three nonzero labels in a zero-sum row, deleting one coordinate
leaves a minimal physical recovery support. Hence all such rows through that
coordinate belong to the already bounded regularized support pool.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortZeroSumSupportIncidence

open Finset PaperP1.Affine PaperP1.DisjointRecoverySubspace PaperP1.RecoveryLabelSupports
  PaperP1.PhysicalLabelSupportCount PaperP1.ZeroSumFreeRepresentations

theorem small_support_unique {V W : Type*} [DecidableEq V] [AddCommGroup W]
    (ℓ : V → W) (A D : Finset V) (hA : A.card ≤ 2) (hD : D ⊆ A) (hDne : D.Nonempty)
    (hnonzero : ∀ v ∈ A, ℓ v ≠ 0) (hsum : (∑ v ∈ A, ℓ v) = ∑ v ∈ D, ℓ v) : D = A := by
  have hcard : (A \ D).card ≤ 1 := by
    rw [card_sdiff_of_subset hD]
    have hd := hDne.card_pos
    omega
  have hzero : (∑ v ∈ A \ D, ℓ v) = 0 := by
    have he := sum_sdiff (f := ℓ) hD
    rw [hsum] at he
    exact add_right_cancel (by simpa only [zero_add] using he :
      (∑ v ∈ A \ D, ℓ v) + (∑ v ∈ D, ℓ v) = 0 + (∑ v ∈ D, ℓ v))
  have hempty : A \ D = ∅ := by
    by_contra hne
    have hc : (A \ D).card = 1 := by have hp := (nonempty_iff_ne_empty.mpr hne).card_pos; omega
    obtain ⟨v, hv⟩ := card_eq_one.mp hc
    have hvA : v ∈ A := (mem_sdiff.mp (by rw [hv]; exact mem_singleton_self v)).1
    rw [hv, sum_singleton] at hzero
    exact hnonzero v hvA hzero
  exact subset_antisymm hD (sdiff_eq_empty_iff_subset.mp hempty)

variable {U V : Type*} [AddCommGroup U] [Module 𝔽₂ U]
  [Fintype V] [DecidableEq V]

local instance dualDecidableEq (M : Submodule 𝔽₂ U) : DecidableEq (Module.Dual 𝔽₂ M) := Classical.decEq _

theorem erased_support_mem_pool (L : V → Module.Dual 𝔽₂ U) (M : Submodule 𝔽₂ U)
    (d : ℕ) (hd : d ≤ 2) (A : Finset V) (v : V) (hv : v ∈ A) (hsize : A.card ≤ d + 1)
    (hnonzero : ∀ w ∈ A, (L w).comp M.subtype ≠ 0)
    (hsum : (∑ w ∈ A, (L w).comp M.subtype) = 0) :
    A.erase v ∈ supportPool (fun w ↦ (L w).comp M.subtype) (labels L M) d ((L v).comp M.subtype) := by
  classical
  let ℓ := fun w ↦ (L w).comp M.subtype
  have hα : ℓ v ≠ 0 := hnonzero v hv
  have hcard : (A.erase v).card ≤ d := by rw [card_erase_of_mem hv]; omega
  have he : (∑ w ∈ A.erase v, ℓ w) = ℓ v := by
    apply (PaperP1.PairFourierIntersection.add_zero_iff _ _).mp
    exact (sum_erase_add A ℓ hv).trans hsum
  obtain ⟨D, hDA, hpool, hDne, _hDcard, _hinj, hDsum⟩ :=
    RegularizedSupportPools.support_pool_contains ℓ (labels L M) d (A.erase v)
      (fun w _ hw ↦ (mem_labels L M _).mpr ⟨hw, w, rfl⟩) hcard (ℓ v) hα he
  have hD : D = A.erase v := small_support_unique ℓ (A.erase v) D (hcard.trans hd) hDA hDne
    (fun w hw ↦ hnonzero w (mem_erase.mp hw).2) (he.trans hDsum.symm)
  simpa only [hD] using hpool

theorem incidence_bound (L : V → Module.Dual 𝔽₂ U) (M : Submodule 𝔽₂ U) (d t : ℕ)
    (hd : 1 ≤ d) (hd₂ : d ≤ 2) (ht : 2 ≤ t)
    (hno : NoDisjointRecovery L M d t) (F : Finset (Finset V))
    (hsize : ∀ A ∈ F, A.card ≤ d + 1)
    (hnonzero : ∀ A ∈ F, ∀ w ∈ A, (L w).comp M.subtype ≠ 0)
    (hsum : ∀ A ∈ F, (∑ w ∈ A, (L w).comp M.subtype) = 0)
    (v : V) (hv : (L v).comp M.subtype ≠ 0) :
    ((F.filter fun A ↦ v ∈ A).card : ℕ) ≤ supportBound d t (t - 1) := by
  classical
  let G := F.filter fun A ↦ v ∈ A
  let pool := supportPool (fun w ↦ (L w).comp M.subtype) (labels L M) d ((L v).comp M.subtype)
  have hinj : Set.InjOn (fun A : Finset V ↦ A.erase v) G := by
    intro A hA B hB he
    have hvA := (mem_filter.mp hA).2
    have hvB := (mem_filter.mp hB).2
    simpa only [insert_erase hvA, insert_erase hvB] using congrArg (insert v) he
  have hsub : G.image (fun A ↦ A.erase v) ⊆ pool := by
    intro D hD
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hD
    obtain ⟨hAF, hvA⟩ := mem_filter.mp hA
    exact erased_support_mem_pool L M d hd₂ A v hvA (hsize A hAF) (hnonzero A hAF) (hsum A hAF)
  have hlabels := noDisjointSums_of_recovery_exclusion L M d t (by omega) hno
  have hmult (α : Module.Dual 𝔽₂ M) (hα : α ∈ labels L M) :
      (fibre (fun w ↦ (L w).comp M.subtype) α).card ≤ t - 1 :=
    coordinate_multiplicity_le L M d t hd hno α ((mem_labels L M α).mp hα).1
  calc
    _ = (G.image (fun A ↦ A.erase v)).card := (card_image_of_injOn hinj).symm
    _ ≤ pool.card := card_le_card hsub
    _ ≤ _ := supportPool_card _ _ d t (t - 1) hlabels hmult _ hv

end PaperP1.ShortZeroSumSupportIncidence
