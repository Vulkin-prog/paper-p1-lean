module

public import PaperP1.Affine.SmallParticipatingConnected
public import PaperP1.Model.ConnectedTargetDependence
public import PaperP1.Model.PrimitiveActiveSeeds

/-! # A dependent pair and a genuinely crossing extra window form a connected triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CrossingPairTriple

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

theorem connected_of_participation (L : ℕ) (T : Finset ℕ) (hT : T.card = 3)
    (hcross : ∀ x ∈ T, squareClassSpace x L ⊓ span (fun y ↦ squareClassSpace y L) (T.erase x) ≠ ⊥) :
    Connected L T := by
  classical
  let : Nonempty T := (card_pos.mp (show 0 < T.card by omega)).coe_sort
  apply SmallParticipatingConnected.connected (fun i : T ↦ squareClassSpace i.val L)
    (by simpa only [Fintype.card_coe] using hT.le)
  intro i
  exact SmallParticipatingConnected.coordinate_relation (fun y ↦ squareClassSpace y L) T i.property
    (hcross i.val i.property)

theorem pair_extension (L : ℕ) (e : Finset ℕ) (he : e.card = 2)
    (hdep : 0 < runRelativeNullity L e) (z : ℕ) (hz : z ∉ e)
    (hcross : span (fun x ↦ squareClassSpace x L) e ⊓ squareClassSpace z L ≠ ⊥) :
    Connected L (e ∪ {z}) := by
  classical
  have hdis : Disjoint e ({z} : Finset ℕ) := disjoint_singleton_right.mpr hz
  have hcard : (e ∪ {z}).card = 3 := by rw [card_union_of_disjoint hdis, he, card_singleton]
  have hprim : Primitive L e := by
    refine ⟨hdep, ?_⟩
    intro B hB
    have hlt := card_lt_card hB
    exact RetainedNullity.nullity_card_le_one (fun x ↦ squareClassSpace x L) B (by omega)
  obtain ⟨r, hr⟩ := PrimitiveRelations.full_relation_of_minimal_nullity
    (fun x ↦ squareClassSpace x L) e hprim.1 hprim.2
  apply connected_of_participation L (e ∪ {z}) hcard
  intro x hx
  rcases mem_union.mp hx with hxe | hxz
  · have hsmall := RelationCoordinateSpan.full_support_intersection
      (fun y ↦ squareClassSpace y L) e r hr (⟨x, hxe⟩ : e)
    have hesub : e.erase x ⊆ (e ∪ {z}).erase x := erase_subset_erase x subset_union_left
    have hmono : squareClassSpace x L ⊓ span (fun y ↦ squareClassSpace y L) (e.erase x) ≤
        squareClassSpace x L ⊓ span (fun y ↦ squareClassSpace y L) ((e ∪ {z}).erase x) :=
      inf_le_inf_left _ (span_mono (fun y ↦ squareClassSpace y L) hesub)
    intro hzero
    exact hsmall (bot_unique (hmono.trans hzero.le))
  · have hxz : x = z := mem_singleton.mp hxz
    subst x
    have herase : (e ∪ {z}).erase z = e := by simp [union_singleton, hz]
    rw [herase, inf_comm]
    exact hcross

theorem connected_positive (L : ℕ) (I : Finset ℕ) (hsize : 2 ≤ I.card)
    (hconn : Connected L I) : 0 < runRelativeNullity L I := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < I.card by omega)
  obtain ⟨y, hy, hyx⟩ := exists_mem_ne (show 1 < I.card by omega) x
  let i : I := ⟨x, hx⟩
  let j : I := ⟨y, hy⟩
  obtain ⟨r, hr, hri⟩ := ConnectedRelations.coordinate_relation (fun i : I ↦ squareClassSpace i.val L)
    hconn i j (fun h ↦ hyx (congrArg Subtype.val h).symm)
  apply Nat.pos_of_ne_zero
  intro hzero
  have hinj := (CompressedBlocks.direct_family_iff_zero_nullity (fun x ↦ squareClassSpace x L) I).mpr hzero
  have hrzero : r = 0 := hinj (hr.trans (map_zero _).symm)
  exact hri (by rw [hrzero]; rfl)

end PaperP1.CrossingPairTriple
