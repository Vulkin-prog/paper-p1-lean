module

public import PaperP1.Asymptotics.AllAlignedTripleMass
public import PaperP1.Model.TripleJointPopulations

/-! # The sharp triple upper bound reduces to three strong nonaligned pairs

All aligned and weak-pair sectors have an internal sharp bound. The literal
remaining population is retained as a nonnegative actual joint-mass term;
no optimal estimate for that term is assumed or asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpTripleResidual

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Hard (L : ℕ) (θ : ℝ) (T : Finset ℕ) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L ∧
    θ * ((L + 1 : ℕ) : ℝ) < (FreeComponentRank.pairIntersectionRank x y L : ℝ)

def hosts (G : Finset ℕ) (L : ℕ) (θ : ℝ) : Finset (Finset ℕ) :=
  (connectedFamilies G L 3).filter (Hard L θ)

def mass (G : Finset ℕ) (L : ℕ) (θ : ℝ) : ℝ :=
  ∑ T ∈ hosts G L θ, infiniteJointMoment L T

theorem mass_le_joint (G : Finset ℕ) (L : ℕ) (θ : ℝ) :
    mass G L θ ≤ TripleJointPopulations.connectedJointMass G L :=
  sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)

theorem uniform_joint_reduction (C ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      0 ≤ TripleJointPopulations.connectedJointMass G L - mass G L θ ∧
      TripleJointPopulations.connectedJointMass G L - mass G L θ ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨θ, hθ, NW, _hNW, hw⟩ := WeakPairTripleMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NA, _hNA, ha⟩ := AllAlignedTripleMass.uniform_mass C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨θ, hθ, 4 + NW + NA + NG + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hwidth := hgeom.2.2.2.1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let S := connectedFamilies G L 3
  let Aligned := fun T : Finset ℕ ↦ ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ CompressedTargetAlignment.Aligned 1 x y L
  let A := S.filter Aligned
  let W := S.filter fun T ↦ ¬ Aligned T ∧ ¬ Hard L θ T
  let H := hosts G L θ
  have hdata (T : Finset ℕ) (hT : T ∈ S) : T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Connected L T := by
    obtain ⟨hTp, hconn⟩ := mem_filter.mp hT
    obtain ⟨hTG, hcard⟩ := mem_powersetCard.mp hTp
    exact ⟨hTG.trans hG, hcard, hconn⟩
  have hcover : S ⊆ (A ∪ W) ∪ H := by
    intro T hT
    by_cases hA : Aligned T
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hT, hA⟩))
    · by_cases hH : Hard L θ T
      · exact mem_union_right _ (mem_filter.mpr ⟨hT, hH⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hT, hA, hH⟩))
  have hA : (∑ T ∈ A, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    apply ha N (by omega) L hband A
    intro T hT
    obtain ⟨hTS, hAligned⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn⟩ := hdata T hTS
    exact ⟨hTN, hcard, hconn, hAligned⟩
  have hW : (∑ T ∈ W, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-3 / 2 + ε / 2) := by
    apply hw N (by omega) L hband W
    intro T hT
    obtain ⟨hTS, hnA, hnH⟩ := mem_filter.mp hT
    obtain ⟨hTN, hcard, hconn⟩ := hdata T hTS
    have hnon (x : ℕ) (hx : x ∈ T) (y : ℕ) (hy : y ∈ T) (hxy : x ≠ y) :
        ¬ CompressedTargetAlignment.Aligned 1 x y L := fun hh ↦ hnA ⟨x, hx, y, hy, hxy, hh⟩
    refine ⟨hTN, hcard, hconn, ?_, ?_⟩
    · intro x hx y hy hxy hnot
      exact False.elim (hnot (ActualOffsetNonalignment.of_nonaligned hL
        (by have hh := (mem_Ico.mp (hTN hx)).1; omega)
        (by have hh := (mem_Ico.mp (hTN hy)).1; omega) (hnon x hx y hy hxy)))
    · by_contra hnweak
      apply hnH
      intro x hx y hy hxy
      refine ⟨hnon x hx y hy hxy, ?_⟩
      exact lt_of_not_ge (fun hsmall ↦ hnweak ⟨x, hx, y, hy, hxy, hsmall⟩)
  have hW' := hW.trans (Real.rpow_le_rpow_of_exponent_le hN1
    (by linarith only [] : -3 / 2 + ε / 2 ≤ -41 / 30 + ε / 2))
  have h0 := sum_le_sum_of_subset_of_nonneg hcover (fun T _ _ ↦ infiniteJointMoment_nonneg L T)
  have h1 := GraphStarWeights.sum_union_le_nonneg A W (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h2 := GraphStarWeights.sum_union_le_nonneg (A ∪ W) H (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  change TripleJointPopulations.connectedJointMass G L ≤ _ at h0
  change _ ≤ (∑ T ∈ A ∪ W, infiniteJointMoment L T) + mass G L θ at h2
  have htotal : TripleJointPopulations.connectedJointMass G L ≤
      mass G L θ + 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) := by
    linarith only [h0, h1, h2, hA, hW']
  have hfactor : 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)
  exact ⟨sub_nonneg.mpr (mass_le_joint G L θ), by linarith only [htotal, hfactor]⟩

end PaperP1.SharpTripleResidual
