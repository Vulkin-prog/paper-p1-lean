module

public import PaperP1.Arithmetic.PrivateEvenImages
public import PaperP1.Algebra.FiniteIntersectionSums
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # Private true values identify the complete even intersection and its coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateEvenIntersection

open Finset PaperP1.Arithmetic PaperP1.FiniteEvenSquareClasses

local instance privateIntersectionPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem space_mono {S T : Finset ℕ} (hST : S ⊆ T) : space S ≤ space T := by
  by_cases hS : S.Nonempty
  · obtain ⟨n, hn⟩ := hS
    rw [space_eq_span S n hn, space_eq_span T n (hST hn)]
    apply Submodule.span_mono
    exact Set.image_mono hST
  · rw [not_nonempty_iff_eq_empty.mp hS, space_empty]
    exact bot_le

theorem space_inter {S T : Finset ℕ} (hprivate : Private (S ∪ T)) :
    space (S ∩ T) = space S ⊓ space T := by
  apply le_antisymm
  · exact le_inf (space_mono inter_subset_left) (space_mono inter_subset_right)
  · intro z hz
    obtain ⟨u, hu, hmapu⟩ := (EvenImage.mem_image_iff (data S) z).mp hz.1
    obtain ⟨v, _, hmapv⟩ := (EvenImage.mem_image_iff (data T) z).mp hz.2
    have hzero (n : S) (hn : n.val ∉ T) : u n = 0 :=
      PrivateEvenImages.coefficient_zero_of_absent hprivate subset_union_left subset_union_right
        u v (hmapu.trans hmapv.symm) n hn
    let w : ↥(S ∩ T) → F₂ := fun n ↦ u ⟨n.val, (mem_inter.mp n.property).1⟩
    have hw : ∑ n : ↥(S ∩ T), w n = 0 :=
      (FiniteIntersectionSums.restrict_sum S T u hzero).trans hu
    have hcombine : EvenImage.combination (data (S ∩ T)) w = z := by
      rw [EvenImage.combination_apply]
      change (∑ n : ↥(S ∩ T), u ⟨n.val, (mem_inter.mp n.property).1⟩ • parityVec n.val) = z
      have hsum := FiniteIntersectionSums.restrict_sum S T (fun n : S ↦ u n • parityVec n.val)
        (fun n hn ↦ by rw [hzero n hn, zero_smul])
      rw [hsum]
      exact hmapu
    exact (EvenImage.mem_image_iff (data (S ∩ T)) z).mpr ⟨w, hw, hcombine⟩

def intersectionMap (S T : Finset ℕ) :
    LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(S ∩ T)) →ₗ[F₂] ↥(space S ⊓ space T) :=
  (EvenImage.evenMap (K := F₂) (data (S ∩ T))).codRestrict (space S ⊓ space T) (by
    intro w
    have hw : EvenImage.evenMap (data (S ∩ T)) w ∈ space (S ∩ T) := ⟨w, rfl⟩
    exact ⟨space_mono inter_subset_left hw, space_mono inter_subset_right hw⟩)

theorem intersectionMap_injective {S T : Finset ℕ} (hprivate : Private (S ∪ T)) :
    Function.Injective (intersectionMap S T) := by
  have hI : Private (S ∩ T) := hprivate.mono (inter_subset_left.trans subset_union_left)
  have hinj := EvenImage.evenMap_injective (K := F₂) (data (S ∩ T)) (combination_injective (S ∩ T) hI)
  intro u v heq
  apply hinj
  exact congrArg Subtype.val heq

theorem intersectionMap_surjective {S T : Finset ℕ} (hprivate : Private (S ∪ T)) :
    Function.Surjective (intersectionMap S T) := by
  intro z
  have hz : z.val ∈ space (S ∩ T) := by rw [space_inter hprivate]; exact z.property
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, Subtype.ext hw⟩

def intersectionEquiv {S T : Finset ℕ} (hprivate : Private (S ∪ T)) :
    LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(S ∩ T)) ≃ₗ[F₂] ↥(space S ⊓ space T) :=
  LinearEquiv.ofBijective (intersectionMap S T) ⟨intersectionMap_injective hprivate, intersectionMap_surjective hprivate⟩

theorem intersection_rank {S T : Finset ℕ} (hprivate : Private (S ∪ T)) :
    Module.finrank F₂ ↥(space S ⊓ space T) = (S ∩ T).card - 1 := by
  rw [← space_inter hprivate]
  exact finrank_space (S ∩ T) (hprivate.mono (inter_subset_left.trans subset_union_left))

theorem actual_intersection_rank {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hprivate : Private (NormalizedWindowSets.union a b x y L)) :
    FreeComponentRank.pairIntersectionRank x y L = (NormalizedUnitCount.units a b x y L).card - 1 := by
  have h := intersection_rank hprivate
  rw [NormalizedWindowSets.space_normalized hb hx, NormalizedWindowSets.space_normalized ha hy,
    NormalizedUnitCount.normalized_intersection_card ha hb (by omega) (by omega)] at h
  exact h

theorem actual_pair_loss {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hprivate : Private (NormalizedWindowSets.union a b x y L)) :
    NormalizedPairRankLoss.pairLoss x y L = (NormalizedUnitCount.units a b x y L).card - 1 := by
  obtain ⟨hxrank, hyrank⟩ := CompressionRank.private_local_ranks ha hb hx hy hprivate
  have hinter := actual_intersection_rank ha hb hx hy hprivate
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (squareClassSpace x L) (squareClassSpace y L)
  unfold NormalizedPairRankLoss.pairLoss FreeComponentRank.pairIntersectionRank at *
  omega

end PaperP1.PrivateEvenIntersection
