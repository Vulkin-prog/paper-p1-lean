module

public import PaperP1.Asymptotics.SeparatedHeightOneRank
public import PaperP1.Model.PositivePairSeparation
public import PaperP1.Asymptotics.StrongAlignedInteriorEdges
public import PaperP1.Asymptotics.WeakExactTripleMassUnderBCN
public import PaperP1.Asymptotics.ConnectedCompressedTripleMassUnderInputs

/-! # Positive strong exact triples lie above a height-two boundary or fixed interior unit channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongExactFiniteChannelCover

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.WeakExactTripleMassUnderBCN

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_cover (θ : ℝ) (hθ : 0 < θ) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ T : Finset ℕ,
      T ⊆ dyadicBlock N → T.card = 3 → Connected L T → StrongExactPair L θ T →
      0 < infiniteJointMoment L T →
      (∃ e ∈ BoundaryAlignedPairs.channel N L 1 2, e ⊆ T) ∨
      ∃ ab ∈ FiniteInteriorUnitEdges.channels Q, T ∈ ConnectedCompressedTripleMassUnderInputs.hosts N ab.1 ab.2 L := by
  obtain ⟨Q, hQ, he⟩ := StrongAlignedInteriorEdges.uniform_edges θ hθ
  refine ⟨Q, hQ, fun C ↦ ?_⟩
  obtain ⟨Ne, _hNe, he⟩ := he C
  obtain ⟨Nx, _hNx, hx⟩ := SeparatedHeightOneRank.uniform_exclusion θ C hθ
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 3 (max Ne (max Nx Ng)), by omega, ?_⟩
  intro N hN L hcrit T hTG hcard hconn hstrong hpos
  have hgeom := hg N (by omega) L hcrit
  have hL : 1 ≤ L := by omega
  have hordered (x y : ℕ) (hxT : x ∈ T) (hyT : y ∈ T) (hxy : x < y)
      (hno : ¬ActualOffsetNonalignment.NoExact x y L)
      (hstrong : θ * ((L + 1 : ℕ) : ℝ) < (FreeComponentRank.pairIntersectionRank x y L : ℝ)) :
      (∃ e ∈ BoundaryAlignedPairs.channel N L 1 2, e ⊆ T) ∨
      ∃ ab ∈ FiniteInteriorUnitEdges.channels Q, T ∈ ConnectedCompressedTripleMassUnderInputs.hosts N ab.1 ab.2 L := by
    have hxN := hTG hxT
    have hyN := hTG hyT
    have hpair : ({x, y} : Finset ℕ) ⊆ T := insert_subset_iff.mpr ⟨hxT, singleton_subset_iff.mpr hyT⟩
    have hsep : x + L ≤ y := PositivePairSeparation.of_joint (by omega) hxy
      (hpos.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L hpair))
    have hLB : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
    have hstrong' : θ * L < (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) :=
      (mul_le_mul_of_nonneg_left hLB hθ.le).trans_lt hstrong
    have halign : CompressedTargetAlignment.Aligned 1 x y L := by
      by_contra hn
      exact hno (ActualOffsetNonalignment.of_nonaligned hL
        (by have hh := (mem_Ico.mp hxN).1; omega) (by have hh := (mem_Ico.mp hyN).1; omega) hn)
    have hnotOne := hx N (by omega) L hcrit x hxN y hyN hxy hsep hstrong'
    by_cases htwo : ({x, y} : Finset ℕ) ∈ BoundaryAlignedPairs.channel N L 1 2
    · exact Or.inl ⟨{x, y}, htwo, hpair⟩
    · right
      have hedge := he N (by omega) L hcrit x y hxN hyN hxy hstrong' halign hnotOne htwo
      obtain ⟨a, b, u, v, hab, heq, hu, hv, hunit, _hsourceGeom⟩ :=
        FiniteInteriorUnitEdges.edge_data (by omega : 0 < N) hedge
      refine ⟨(a, b), hab, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hTG, hcard⟩, hconn⟩,
        (u, v), mem_filter.mpr ⟨mem_product.mpr ⟨hu, hv⟩, hunit⟩, ?_⟩⟩
      rw [← heq]
      exact hpair
  obtain ⟨x, hxT, y, hyT, hxy, hno, hbig⟩ := hstrong
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact hordered x y hxT hyT hlt hno hbig
  · apply hordered y x hyT hxT hgt (fun hn ↦ hno hn.symm)
    change θ * ((L + 1 : ℕ) : ℝ) < (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace x L) : ℝ)
    rw [inf_comm]
    exact hbig

end PaperP1.StrongExactFiniteChannelCover
