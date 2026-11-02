module

public import PaperP1.Model.PrincipalChannelEdges
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Actual principal edges retain exact units and bounded geometry in either orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalEdgeGeometry

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateChannelSources

def channels : Finset (ℕ × ℕ) := {(2, 3), (3, 4)}

theorem channel_properties {ab : ℕ × ℕ} (hab : ab ∈ channels) :
    0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ ab.1 ≤ 4 ∧ ab.2 ≤ 4 := by
  have hh : ab = (2, 3) ∨ ab = (3, 4) := by simpa only [channels, mem_insert, mem_singleton] using hab
  rcases hh with rfl | rfl <;> norm_num

theorem channel_data {N H a b L : ℕ} (hN : 0 < N) {e : Finset ℕ}
    (he : e ∈ CompatibleChannelEdges.edges N H a b L) :
    ∃ x y : ℕ, e = {x, y} ∧ x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
      (NormalizedUnitCount.units a b x y L).Nonempty ∧ EnlargedPairGeometry.Geometric a b x y L := by
  obtain ⟨xy, hxy, heq⟩ := mem_image.mp (mem_filter.mp he).1
  obtain ⟨hx, hy, hcard, _hprivate⟩ := mem_goodSources.mp hxy
  refine ⟨xy.1, xy.2, heq.symm, hx, hy, card_pos.mp (by omega), ?_⟩
  have hh := FixedChannelLinearCount.unit_alignment hN (good_sources_subset_unitSources N H a b L hxy)
  simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hh

theorem edge_data {N H L : ℕ} (hN : 0 < N) {e : Finset ℕ} (he : e ∈ PrincipalChannelEdges.edges N H L) :
    ∃ a b x y : ℕ, (a, b) ∈ channels ∧ e = {x, y} ∧ x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧
      (NormalizedUnitCount.units a b x y L).Nonempty ∧ EnlargedPairGeometry.Geometric a b x y L := by
  rcases mem_union.mp he with he | he
  · obtain ⟨x, y, heq, hx, hy, hu, hg⟩ := channel_data hN he
    exact ⟨2, 3, x, y, by simp [channels], heq, hx, hy, hu, hg⟩
  · obtain ⟨x, y, heq, hx, hy, hu, hg⟩ := channel_data hN he
    exact ⟨3, 4, x, y, by simp [channels], heq, hx, hy, hu, hg⟩

theorem pair_geometry {N H L u v : ℕ} (hN : 0 < N) {e : Finset ℕ}
    (he : e ∈ PrincipalChannelEdges.edges N H L) (heq : e = {u, v}) (huv : u ≠ v) :
    ∃ r s : ℕ, 0 < r ∧ r ≤ 4 ∧ 0 < s ∧ s ≤ 4 ∧ EnlargedPairGeometry.Geometric r s u v L := by
  obtain ⟨a, b, x, y, hab, hxy, _hx, _hy, _hu, hgeom⟩ := edge_data hN he
  obtain ⟨ha, horder, _hinterior, _hcop, ha4, hb4⟩ := channel_properties hab
  have hb : 0 < b := ha.trans horder
  have humem : u ∈ ({x, y} : Finset ℕ) := by rw [← hxy, heq]; simp
  have hvmem : v ∈ ({x, y} : Finset ℕ) := by rw [← hxy, heq]; simp
  simp only [mem_insert, mem_singleton] at humem hvmem
  have hor : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by omega
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, ha, ha4, hb, hb4, hgeom⟩
  · exact ⟨b, a, hb, hb4, ha, ha4, (EnlargedPairGeometry.geometric_swap a b _ _ L).mp hgeom⟩

end PaperP1.PrincipalEdgeGeometry
