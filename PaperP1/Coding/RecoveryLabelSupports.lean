module

public import PaperP1.Coding.DisjointRecoverySubspace
public import PaperP1.Combinatorics.ZeroSumFreeRepresentations

/-! # Lifting disjoint label supports back to physical coordinate supports -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RecoveryLabelSupports

open Finset PaperP1.DisjointRecoverySubspace PaperP1.ZeroSumFreeRepresentations

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
variable [Fintype V] [DecidableEq V]

local instance recoverySupportDecidableEq (M : Submodule K U) : DecidableEq (Module.Dual K M) :=
  Classical.decEq _

def labels (L : V → Module.Dual K U) (M : Submodule K U) : Finset (Module.Dual K M) := by
  classical
  exact (univ.image fun v ↦ (L v).comp M.subtype).erase 0

omit [DecidableEq V] in
theorem mem_labels (L : V → Module.Dual K U) (M : Submodule K U) (α : Module.Dual K M) :
    α ∈ labels L M ↔ α ≠ 0 ∧ ∃ v, (L v).comp M.subtype = α := by
  classical
  simp only [labels, mem_erase, mem_image, mem_univ, true_and]

theorem noDisjointSums_of_recovery_exclusion (L : V → Module.Dual K U) (M : Submodule K U)
    (d t : ℕ) (ht : 1 ≤ t) (hno : NoDisjointRecovery L M d t) :
    NoDisjointSums (labels L M) d t := by
  classical
  intro α hα E hsets hEt hdisj
  have hEnonempty : E.Nonempty := card_pos.mp (by rw [hEt]; omega)
  obtain ⟨A0, hA0E⟩ := hEnonempty
  have hA0nonempty : A0.Nonempty := card_pos.mp (by have h := (hsets A0 hA0E).2.1; omega)
  obtain ⟨a0, ha0⟩ := hA0nonempty
  obtain ⟨_, v0, _⟩ := (mem_labels L M a0).mp ((hsets A0 hA0E).1 ha0)
  let f : V → Module.Dual K M := fun v ↦ (L v).comp M.subtype
  let r : Module.Dual K M → V := fun a ↦ if h : ∃ v, f v = a then h.choose else v0
  have hr (a : Module.Dual K M) (ha : a ∈ labels L M) : f (r a) = a := by
    have hex : ∃ v, f v = a := (mem_labels L M a).mp ha |>.2
    simp only [r, dite_eq_left hex]
    exact hex.choose_spec
  have hinj : Set.InjOn r (↑(labels L M) : Set (Module.Dual K M)) := by
    intro a ha b hb heq
    have h := congrArg f heq
    simpa only [hr a ha, hr b hb] using h
  let e : Fin t ≃ E := (Finset.equivFinOfCardEq hEt).symm
  let B : Fin t → Finset V := fun j ↦ (e j).val.image r
  have hcard (j : Fin t) : (B j).card = (e j).val.card := by
    apply card_image_iff.mpr
    intro a ha b hb heq
    exact hinj ((hsets _ (e j).property).1 ha) ((hsets _ (e j).property).1 hb) heq
  apply hno α hα B
  · intro j _ k _ hjk
    apply disjoint_left.mpr
    intro v hvj hvk
    obtain ⟨a, ha, hav⟩ := mem_image.mp hvj
    obtain ⟨b, hb, hbv⟩ := mem_image.mp hvk
    have hab : a = b := hinj ((hsets _ (e j).property).1 ha) ((hsets _ (e k).property).1 hb)
      (hav.trans hbv.symm)
    have hneq : (e j).val ≠ (e k).val := fun h ↦ hjk (e.injective (Subtype.ext h))
    have hD := hdisj (e j).property (e k).property hneq
    rw [hab] at ha
    exact disjoint_left.mp hD ha hb
  · intro j
    rw [hcard j]
    exact ⟨(hsets _ (e j).property).2.1, (hsets _ (e j).property).2.2.1⟩
  · intro j
    change (∑ v ∈ (e j).val.image r, f v) = α
    rw [sum_image]
    · calc
        _ = ∑ a ∈ (e j).val, a := by
          apply sum_congr rfl
          intro a ha
          exact hr a ((hsets _ (e j).property).1 ha)
        _ = _ := (hsets _ (e j).property).2.2.2
    · intro a ha b hb heq
      exact hinj ((hsets _ (e j).property).1 ha) ((hsets _ (e j).property).1 hb) heq

end PaperP1.RecoveryLabelSupports
