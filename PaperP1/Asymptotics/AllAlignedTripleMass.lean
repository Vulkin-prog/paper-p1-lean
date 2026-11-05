module

public import PaperP1.Asymptotics.WeakPairTripleMass
public import PaperP1.Asymptotics.StrongAlignedSharpMass

/-! # Every connected triple containing any literal aligned pair has sharp mass

The complete cubic height range in the alignment definition is retained.
No fixed family of rational slopes or actual exact unit is required.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllAlignedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.StrongAlignedSharpMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ P : Finset (Finset ℕ),
      (∀ T ∈ P, T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Connected L T ∧
        ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ CompressedTargetAlignment.Aligned 1 x y L) →
      (∑ T ∈ P, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨θ, hθ, NW, _hNW, hw⟩ := WeakPairTripleMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨_Q, _hQ, NS, _hNS, hs⟩ := StrongAlignedSharpMass.article_14_4 θ C (ε / 2) hθ (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NW + NS + NG + NF, by omega, ?_⟩
  intro N hN L hcrit P hP
  obtain ⟨_hN2, _hBmin, _hB2, hwidth, _hscale⟩ := hg N (by omega) L hcrit
  have hL : 1 ≤ L := by omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let S := P.filter (StrongAligned L θ)
  let R := P.filter fun T ↦ ¬ StrongAligned L θ T
  have hstrong : (∑ T ∈ S, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    apply hs N (by omega) L hcrit S
    intro T hT
    obtain ⟨hTP, hstrong⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn, _hsource⟩ := hP T hTP
    exact ⟨hTN, hcard, hconn, hstrong⟩
  have hrest : (∑ T ∈ R, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    apply hw N (by omega) L hcrit R
    intro T hT
    obtain ⟨hTP, hnstrong⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn, hsource⟩ := hP T hTP
    have hweak_aligned (x : ℕ) (hx : x ∈ T) (y : ℕ) (hy : y ∈ T) (hxy : x ≠ y)
        (halign : CompressedTargetAlignment.Aligned 1 x y L) :
        (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ) := by
      by_contra hh
      apply hnstrong
      exact (strong_aligned_iff_unordered L θ T).mpr
        ⟨x, hx, y, hy, hxy, halign, (lt_of_not_ge hh).le⟩
    refine ⟨hTN, hcard, hconn, ?_, ?_⟩
    · intro x hx y hy hxy hnot
      apply hweak_aligned x hx y hy hxy
      by_contra hnon
      exact hnot (ActualOffsetNonalignment.of_nonaligned hL
        (by have hh := (mem_Ico.mp (hTN hx)).1; omega)
        (by have hh := (mem_Ico.mp (hTN hy)).1; omega) hnon)
    · obtain ⟨x, hx, y, hy, hxy, halign⟩ := hsource
      exact ⟨x, hx, y, hy, hxy, hweak_aligned x hx y hy hxy halign⟩
  have hrest' := hrest.trans (Real.rpow_le_rpow_of_exponent_le hN1
    (by linarith only [] : -3 / 2 + ε / 2 ≤ -41 / 30 + ε / 2))
  have hpart := sum_filter_add_sum_filter_not P (StrongAligned L θ) (infiniteJointMoment L)
  have hfactor : 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)
  change (∑ T ∈ S, infiniteJointMoment L T) + (∑ T ∈ R, infiniteJointMoment L T) = _ at hpart
  linarith only [hstrong, hrest', hpart, hfactor]

end PaperP1.AllAlignedTripleMass
