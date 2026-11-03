module

public import PaperP1.Arithmetic.EvenIndependentValues
public import PaperP1.Arithmetic.PrivateEvenIntersection
public import PaperP1.Algebra.EvenImageEmbeddingDefect

/-! # Even independence of a literal union already identifies the exact even-space intersection -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenIndependentIntersection

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance evenIntersectionPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem coefficient_zero_of_absent {S T : Finset ℕ} (hind : EvenIndependentValues.Independent (S ∪ T))
    (u : LinearMap.ker (EvenSupportRank.sumMap F₂ S)) (v : LinearMap.ker (EvenSupportRank.sumMap F₂ T))
    (heq : EvenImage.evenMap (data S) u = EvenImage.evenMap (data T) v)
    (n : S) (hnT : n.val ∉ T) : u.val n = 0 := by
  let eS : S ↪ ↥(S ∪ T) := ⟨fun n ↦ ⟨n.val, mem_union.mpr (Or.inl n.property)⟩, by
    intro n m h
    exact Subtype.ext (congrArg (fun n : ↥(S ∪ T) ↦ n.val) h)⟩
  let eT : T ↪ ↥(S ∪ T) := ⟨fun n ↦ ⟨n.val, mem_union.mpr (Or.inr n.property)⟩, by
    intro n m h
    exact Subtype.ext (congrArg (fun n : ↥(S ∪ T) ↦ n.val) h)⟩
  have hext : FinitePiExtension.extendEven eS u = FinitePiExtension.extendEven eT v := by
    apply hind
    rw [FinitePiExtension.evenMap_extend eS (data S) (data (S ∪ T)) (fun _ ↦ rfl),
      FinitePiExtension.evenMap_extend eT (data T) (data (S ∪ T)) (fun _ ↦ rfl)]
    exact heq
  have hpoint := congrArg (fun w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(S ∪ T)) ↦ w.val (eS n)) hext
  change FinitePiExtension.extend eS u.val (eS n) = FinitePiExtension.extend eT v.val (eS n) at hpoint
  rw [FinitePiExtension.extend_at, EvenImageEmbeddingDefect.extend_outside eT v.val (eS n) (by
    intro m h
    have hval : m.val = n.val := congrArg Subtype.val h
    exact hnT (hval ▸ m.property))] at hpoint
  exact hpoint

theorem space_inter {S T : Finset ℕ} (hind : EvenIndependentValues.Independent (S ∪ T)) :
    space (S ∩ T) = space S ⊓ space T := by
  apply le_antisymm
  · exact le_inf (PrivateEvenIntersection.space_mono inter_subset_left)
      (PrivateEvenIntersection.space_mono inter_subset_right)
  · intro z hz
    obtain ⟨u, hmapu⟩ := hz.1
    obtain ⟨v, hmapv⟩ := hz.2
    have hout (n : S) (hnT : n.val ∉ T) : u.val n = 0 :=
      coefficient_zero_of_absent hind u v (hmapu.trans hmapv.symm) n hnT
    have hu : ∑ n : S, u.val n = 0 := by
      simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using u.property
    let w : ↥(S ∩ T) → F₂ := fun n ↦ u.val ⟨n.val, (mem_inter.mp n.property).1⟩
    have hw : ∑ n : ↥(S ∩ T), w n = 0 := (FiniteIntersectionSums.restrict_sum S T u.val hout).trans hu
    apply (EvenImage.mem_image_iff (data (S ∩ T)) z).mpr
    refine ⟨w, hw, ?_⟩
    rw [EvenImage.combination_apply]
    change (∑ n : ↥(S ∩ T), u.val ⟨n.val, (mem_inter.mp n.property).1⟩ • parityVec n.val) = z
    rw [FiniteIntersectionSums.restrict_sum S T (fun n : S ↦ u.val n • parityVec n.val)
      (fun n hn ↦ by rw [hout n hn, zero_smul])]
    exact hmapu

theorem disjoint_of_inter_card_le_one {S T : Finset ℕ} (hind : EvenIndependentValues.Independent (S ∪ T))
    (hcard : (S ∩ T).card ≤ 1) : Disjoint (space S) (space T) := by
  have hzero : space (S ∩ T) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨w, hmap⟩ := hz
    have hw0 : w = 0 := by
      apply Subtype.ext
      funext n
      have hsum : (∑ m : ↥(S ∩ T), w.val m) = w.val n := by
        apply sum_eq_single n
        · intro m _hm hmn
          have hvals : m.val = n.val := card_le_one.mp hcard _ m.property _ n.property
          exact (hmn (Subtype.ext hvals)).elim
        · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
      have htotal : (∑ m : ↥(S ∩ T), w.val m) = 0 := by
        simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property
      exact hsum.symm.trans htotal
    rw [hw0, map_zero] at hmap
    exact hmap.symm
  apply Submodule.disjoint_def.mpr
  intro z hzS hzT
  have hz : z ∈ space (S ∩ T) := (space_inter hind).symm ▸ ⟨hzS, hzT⟩
  rw [hzero] at hz
  exact hz

end PaperP1.EvenIndependentIntersection
