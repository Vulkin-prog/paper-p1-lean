module

public import PaperP1.Model.PrincipalEdgeGeometry
public import PaperP1.Combinatorics.TwoEdgeTripleCover

/-! # Every actual three-element family containing two principal edges has bounded endpoint target geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPrincipalTriples

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (N H L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 3).filter fun T ↦
    2 ≤ ((PrincipalChannelEdges.edges N H L).filter fun e ↦ e ⊆ T).card

def mass (N H L : ℕ) : ℝ := ∑ T ∈ families N H L, infiniteJointMoment L T

theorem family_data {N H L : ℕ} {T : Finset ℕ} (hT : T ∈ families N H L) :
    T ⊆ dyadicBlock N ∧ T.card = 3 ∧
      2 ≤ ((PrincipalChannelEdges.edges N H L).filter fun e ↦ e ⊆ T).card := by
  obtain ⟨hp, htwo⟩ := mem_filter.mp hT
  exact ⟨(mem_powersetCard.mp hp).1, (mem_powersetCard.mp hp).2, htwo⟩

theorem source_data {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N)
    {T : Finset ℕ} (hT : T ∈ families N H L) :
    ∃ a b x y z r s : ℕ, (a, b) ∈ PrincipalEdgeGeometry.channels ∧ T = {x, y, z} ∧
      (NormalizedUnitCount.units a b x y L).Nonempty ∧ 0 < r ∧ r ≤ 4 ∧ 0 < s ∧ s ≤ 4 ∧
      (EnlargedPairGeometry.Geometric r s x z L ∨ EnlargedPairGeometry.Geometric r s y z L) := by
  obtain ⟨_hsub, hcard, htwo⟩ := family_data hT
  obtain ⟨e, he, f, hf, hef⟩ := one_lt_card.mp (show 1 <
    ((PrincipalChannelEdges.edges N H L).filter fun e ↦ e ⊆ T).card by omega)
  obtain ⟨heE, heT⟩ := mem_filter.mp he
  obtain ⟨hfE, hfT⟩ := mem_filter.mp hf
  have hpair := PrincipalChannelEdges.subset_pairs (H := H) hN hlarge
  have hecard := (mem_powersetCard.mp (hpair heE)).2
  have hfcard := (mem_powersetCard.mp (hpair hfE)).2
  obtain ⟨z, _hzT, _hze, hTez⟩ := TwoEdgeTripleCover.third_vertex hcard hecard heT
  obtain ⟨u, hue, hfeq, huz⟩ := TwoEdgeTripleCover.other_edge hecard hfcard hfT hef hTez
  obtain ⟨a, b, x, y, hab, heq, _hx, _hy, hunit, _hgeom⟩ := PrincipalEdgeGeometry.edge_data (by omega : 0 < N) heE
  obtain ⟨r, s, hr, hr4, hs, hs4, htarget⟩ := PrincipalEdgeGeometry.pair_geometry (by omega : 0 < N) hfE hfeq huz
  have hfamily : T = {x, y, z} := by rw [hTez, heq]; simp only [insert_union, singleton_union]
  have huxy : u = x ∨ u = y := by simpa only [heq, mem_insert, mem_singleton] using hue
  refine ⟨a, b, x, y, z, r, s, hab, hfamily, hunit, hr, hr4, hs, hs4, ?_⟩
  rcases huxy with rfl | rfl
  · exact Or.inl htarget
  · exact Or.inr htarget

end PaperP1.SharedPrincipalTriples
