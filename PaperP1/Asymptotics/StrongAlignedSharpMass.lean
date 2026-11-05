module

public import PaperP1.Asymptotics.SharpFiniteInteriorMass
public import PaperP1.Asymptotics.StrongExactFiniteChannelCover
public import PaperP1.Asymptotics.HeightTwoBoundaryJointMass

/-! # Main14.4 for every strongly geometrically aligned original pair

The non-strict original rank threshold is kept. Exact units are deduced,
and the height-one and height-two boundary cases are handled separately.
No BCN premise is used for this aligned-sector theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongAlignedSharpMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def StrongAligned (L : ℕ) (θ : ℝ) (T : Finset ℕ) : Prop :=
  ∃ x ∈ T, ∃ y ∈ T, x < y ∧ CompressedTargetAlignment.Aligned 1 x y L ∧
    θ * ((L + 1 : ℕ) : ℝ) ≤ (FreeComponentRank.pairIntersectionRank x y L : ℝ)

theorem aligned_swap (D x y L : ℕ) :
    CompressedTargetAlignment.Aligned D x y L ↔ CompressedTargetAlignment.Aligned D y x L := by
  constructor <;> rintro ⟨r, s, hr, hs, hcop, hrB, hsB, hg⟩
  · refine ⟨s, r, hs, hr, hcop.symm, hsB, hrB, ?_⟩
    simpa only [Nat.add_comm s r, abs_sub_comm] using hg
  · refine ⟨s, r, hs, hr, hcop.symm, hsB, hrB, ?_⟩
    simpa only [Nat.add_comm s r, abs_sub_comm] using hg

theorem strong_aligned_iff_unordered (L : ℕ) (θ : ℝ) (T : Finset ℕ) :
    StrongAligned L θ T ↔ ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ CompressedTargetAlignment.Aligned 1 x y L ∧
      θ * ((L + 1 : ℕ) : ℝ) ≤ (FreeComponentRank.pairIntersectionRank x y L : ℝ) := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy, halign, hrank⟩
    exact ⟨x, hx, y, hy, hxy.ne, halign, hrank⟩
  · rintro ⟨x, hx, y, hy, hxy, halign, hrank⟩
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact ⟨x, hx, y, hy, hlt, halign, hrank⟩
    · refine ⟨y, hy, x, hx, hgt, (aligned_swap 1 x y L).mp halign, ?_⟩
      change θ * ((L + 1 : ℕ) : ℝ) ≤ (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace x L) : ℝ)
      rw [inf_comm]
      exact hrank

theorem article_14_4 (θ C ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
        (∀ T ∈ F, T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Connected L T ∧ StrongAligned L θ T) →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  have hhalf : 0 < θ / 2 := by positivity
  obtain ⟨Q, hQ, he⟩ := StrongAlignedInteriorEdges.uniform_edges (θ / 2) hhalf
  obtain ⟨NE, _hNE, he⟩ := he C
  obtain ⟨NX, _hNX, hx⟩ := SeparatedHeightOneRank.uniform_exclusion (θ / 2) C hhalf
  obtain ⟨NI, _hNI, hi⟩ := SharpFiniteInteriorMass.uniform_mass Q C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := HeightTwoBoundaryJointMass.uniform_triples C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨Q, hQ, ?_⟩
  refine ⟨max 4 (max NE (max NX (max NI (max NB (max NG NF))))), by omega, ?_⟩
  intro N hN L hcrit F hF
  let P := F.filter fun T ↦ 0 < infiniteJointMoment L T
  let B := P.filter fun T ↦ ∃ e ∈ BoundaryAlignedPairs.channel N L 1 2, e ⊆ T
  let I := P.filter fun T ↦ T ∈ FiniteCompressedInteriorMass.hosts N L Q
  have hPF : P ⊆ F := filter_subset _ _
  have hsum : (∑ T ∈ P, infiniteJointMoment L T) = ∑ T ∈ F, infiniteJointMoment L T := by
    apply sum_subset hPF
    intro T hTF hnot
    have hh : ¬0 < infiniteJointMoment L T := fun hh ↦ hnot (mem_filter.mpr ⟨hTF, hh⟩)
    exact le_antisymm (le_of_not_gt hh) (infiniteJointMoment_nonneg L T)
  have hcover : P ⊆ B ∪ I := by
    intro T hT
    obtain ⟨hTF, hpos⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn, x, hxT, y, hyT, hxy, halign, hbig⟩ := hF T hTF
    have hxN := hTN hxT
    have hyN := hTN hyT
    have hL : 1 ≤ L := by have hh := (hg N (by omega) L hcrit).2.2.1; omega
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hstrong : (θ / 2) * L < (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) := by
      change θ * ((L + 1 : ℕ) : ℝ) ≤ (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) at hbig
      push_cast at hbig
      nlinarith only [hbig, mul_pos hθ hLR]
    have hpair : ({x, y} : Finset ℕ) ⊆ T := insert_subset_iff.mpr ⟨hxT, singleton_subset_iff.mpr hyT⟩
    have hsep : x + L ≤ y := PositivePairSeparation.of_joint (by omega) hxy
      (hpos.trans_le (MissingBlockProbabilities.infiniteJointMoment_antitone L hpair))
    have hnotOne := hx N (by omega) L hcrit x hxN y hyN hxy hsep hstrong
    by_cases htwo : ({x, y} : Finset ℕ) ∈ BoundaryAlignedPairs.channel N L 1 2
    · exact mem_union_left _ (mem_filter.mpr ⟨hT, {x, y}, htwo, hpair⟩)
    · have hedge := he N (by omega) L hcrit x y hxN hyN hxy hstrong halign hnotOne htwo
      obtain ⟨a, b, u, v, hab, heq, hu, hv, hunit, _hsourceGeom⟩ :=
        FiniteInteriorUnitEdges.edge_data (by omega : 0 < N) hedge
      apply mem_union_right
      apply mem_filter.mpr
      refine ⟨hT, FiniteCompressedInteriorMass.mem_hosts.mpr ⟨(a, b), hab, ?_⟩⟩
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hTN, hcard⟩, hconn⟩,
        (u, v), mem_filter.mpr ⟨mem_product.mpr ⟨hu, hv⟩, hunit⟩, ?_⟩
      rw [← heq]
      exact hpair
  have hboundary : (∑ T ∈ B, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    have hh := hb N (by omega) L hcrit B (by
      intro T hT
      obtain ⟨hTP, hTB⟩ := mem_filter.mp hT
      obtain ⟨hTN, hcard, _hconn, _hstrong⟩ := hF T (hPF hTP)
      exact ⟨hTN, hcard, hTB⟩)
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only []))
  have hinterior : (∑ T ∈ I, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg (fun _ hT ↦ (mem_filter.mp hT).2)
      (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hi N (by omega) L hcrit)
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun T _ _ ↦ infiniteJointMoment_nonneg L T)
  have h1 := GraphStarWeights.sum_union_le_nonneg B I (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have hfactor : 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)
  rw [← hsum]
  linarith only [hboundary, hinterior, h0, h1, hfactor]

end PaperP1.StrongAlignedSharpMass
