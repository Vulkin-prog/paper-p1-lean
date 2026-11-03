module

public import PaperP1.Model.AllAlignedPairs
public import PaperP1.Combinatorics.TwoEdgeTripleCover

/-! # Actual edges in finitely many interior coprime channels and their three-vertex hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteInteriorUnitEdges

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channels (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 Q ×ˢ Icc 1 Q).filter fun ab ↦ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2

def edges (N L Q : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 2).filter fun e ↦ ∃ ab ∈ channels Q, ∃ x y : ℕ,
    e = {x, y} ∧ (NormalizedUnitCount.units ab.1 ab.2 x y L).Nonempty

theorem channel_data {Q : ℕ} {ab : ℕ × ℕ} (hab : ab ∈ channels Q) :
    0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ ab.1 ≤ Q ∧ ab.2 ≤ Q := by
  obtain ⟨habI, hlt, hint, hcop⟩ := mem_filter.mp hab
  obtain ⟨ha, hb⟩ := mem_product.mp habI
  exact ⟨(mem_Icc.mp ha).1, hlt, hint, hcop, (mem_Icc.mp ha).2, (mem_Icc.mp hb).2⟩

theorem edge_data {N L Q : ℕ} (hN : 0 < N) {e : Finset ℕ} (he : e ∈ edges N L Q) :
    ∃ a b x y : ℕ, (a, b) ∈ channels Q ∧ e = {x, y} ∧
      x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
      (NormalizedUnitCount.units a b x y L).Nonempty ∧ EnlargedPairGeometry.Geometric a b x y L := by
  obtain ⟨heN, ab, hab, x, y, heq, hu⟩ := mem_filter.mp he
  have hsub := (mem_powersetCard.mp heN).1
  have hx : x ∈ dyadicBlock N := hsub (by rw [heq]; simp)
  have hy : y ∈ dyadicBlock N := hsub (by rw [heq]; simp)
  refine ⟨ab.1, ab.2, x, y, hab, heq, hx, hy, hu, ?_⟩
  have hg := FixedChannelLinearCount.unit_alignment (a := ab.1) (b := ab.2) (L := L) hN
    (xy := (x, y)) (mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, hu⟩)
  simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hg

theorem pair_geometry {N L Q u v : ℕ} (hN : 0 < N) {e : Finset ℕ}
    (he : e ∈ edges N L Q) (heq : e = {u, v}) (huv : u ≠ v) :
    ∃ r s : ℕ, 0 < r ∧ r ≤ Q ∧ 0 < s ∧ s ≤ Q ∧ EnlargedPairGeometry.Geometric r s u v L := by
  obtain ⟨a, b, x, y, hab, hxy, _hx, _hy, _hu, hgeom⟩ := edge_data hN he
  obtain ⟨ha, horder, _hinterior, _hcop, haQ, hbQ⟩ := channel_data hab
  have hb : 0 < b := ha.trans horder
  have humem : u ∈ ({x, y} : Finset ℕ) := by rw [← hxy, heq]; simp
  have hvmem : v ∈ ({x, y} : Finset ℕ) := by rw [← hxy, heq]; simp
  simp only [mem_insert, mem_singleton] at humem hvmem
  have hor : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by omega
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, ha, haQ, hb, hbQ, hgeom⟩
  · exact ⟨b, a, hb, hbQ, ha, haQ, (EnlargedPairGeometry.geometric_swap a b _ _ L).mp hgeom⟩

theorem triple_source {N L Q : ℕ} (hN : 0 < N) {T : Finset ℕ} (hcard : T.card = 3)
    (htwo : 2 ≤ ((edges N L Q).filter fun e ↦ e ⊆ T).card) :
    ∃ a b x y z r s : ℕ, (a, b) ∈ channels Q ∧ T = {x, y, z} ∧
      (NormalizedUnitCount.units a b x y L).Nonempty ∧ 0 < r ∧ r ≤ Q ∧ 0 < s ∧ s ≤ Q ∧
      (EnlargedPairGeometry.Geometric r s x z L ∨ EnlargedPairGeometry.Geometric r s y z L) := by
  obtain ⟨e, he, f, hf, hef⟩ := one_lt_card.mp (show 1 <
    ((edges N L Q).filter fun e ↦ e ⊆ T).card by omega)
  obtain ⟨heE, heT⟩ := mem_filter.mp he
  obtain ⟨hfE, hfT⟩ := mem_filter.mp hf
  have hecard := (mem_powersetCard.mp (mem_filter.mp heE).1).2
  have hfcard := (mem_powersetCard.mp (mem_filter.mp hfE).1).2
  obtain ⟨z, _hzT, _hze, hTez⟩ := TwoEdgeTripleCover.third_vertex hcard hecard heT
  obtain ⟨u, hue, hfeq, huz⟩ := TwoEdgeTripleCover.other_edge hecard hfcard hfT hef hTez
  obtain ⟨a, b, x, y, hab, heq, _hx, _hy, hunit, _hgeom⟩ := edge_data hN heE
  obtain ⟨r, s, hr, hrQ, hs, hsQ, htarget⟩ := pair_geometry hN hfE hfeq huz
  have hfamily : T = {x, y, z} := by rw [hTez, heq]; simp only [insert_union, singleton_union]
  have huxy : u = x ∨ u = y := by simpa only [heq, mem_insert, mem_singleton] using hue
  refine ⟨a, b, x, y, z, r, s, hab, hfamily, hunit, hr, hrQ, hs, hsQ, ?_⟩
  rcases huxy with rfl | rfl
  · exact Or.inl htarget
  · exact Or.inr htarget

end PaperP1.FiniteInteriorUnitEdges
