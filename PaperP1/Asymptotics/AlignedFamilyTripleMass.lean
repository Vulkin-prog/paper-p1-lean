module

public import PaperP1.Asymptotics.WeakPairTripleMass
public import PaperP1.Asymptotics.StrongAlignedSharpMass

/-! # The complete fixed geometrically aligned triple family, without BCN

A fixed channel gives an aligned source pair even if it has no exact unit.
After the strong aligned sector is removed, this supplies a weak pair and
caps the full triple rank. The internal weak-pair theorem handles the rest.
Irregular windows, bad normalization and exact-distance contacts remain.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedFamilyTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies PaperP1.StrongAlignedSharpMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (N L : ℕ) (F : Finset (ℕ × ℕ)) : Finset (Finset ℕ) :=
  (connectedFamilies (dyadicBlock N) L 3).filter fun T ↦
    ∃ ab ∈ F, ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ EnlargedPairGeometry.Geometric ab.1 ab.2 x y L

def mass (N L : ℕ) (F : Finset (ℕ × ℕ)) : ℝ :=
  ∑ T ∈ families N L F, infiniteJointMoment L T

theorem positive_filter_eq (N L : ℕ) (F : Finset (ℕ × ℕ)) :
    (∑ T ∈ (families N L F).filter (fun T ↦ 0 < infiniteJointMoment L T), infiniteJointMoment L T) = mass N L F := by
  apply sum_subset (filter_subset _ _)
  intro T hT hnot
  have hz : ¬0 < infiniteJointMoment L T := fun hh ↦ hnot (mem_filter.mpr ⟨hT, hh⟩)
  exact le_antisymm (le_of_not_gt hz) (infiniteJointMoment_nonneg L T)

theorem uniform_mass (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ P : Finset (Finset ℕ),
      (∀ T ∈ P, T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Connected L T ∧
        ∃ ab ∈ F, ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ EnlargedPairGeometry.Geometric ab.1 ab.2 x y L) →
      (∑ T ∈ P, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨θ, hθ, NW, _hNW, hw⟩ := WeakPairTripleMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨_Q, _hQ, NS, _hNS, hs⟩ := StrongAlignedSharpMass.article_14_4 θ C (ε / 2) hθ (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max (F.sup Prod.fst) (F.sup Prod.snd))
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NW + NS + NG + NF, by omega, ?_⟩
  intro N hN L hcrit P hP
  obtain ⟨_hN2, hBmin, _hB2, hwidth, _hscale⟩ := hg N (by omega) L hcrit
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
    · obtain ⟨ab, hab, x, hx, y, hy, hxy, hgeom⟩ := hsource
      have haB : ab.1 ≤ L + 1 := (Finset.le_sup hab).trans ((le_max_left _ _).trans hBmin)
      have hbB : ab.2 ≤ L + 1 := (Finset.le_sup hab).trans ((le_max_right _ _).trans hBmin)
      have hpow : L + 1 ≤ (L + 1) ^ 3 := le_self_pow (by omega) (by decide : 3 ≠ 0)
      have halign := CompressedTargetAlignment.of_geometric (hF ab hab).1
        ((hF ab hab).1.trans (hF ab hab).2.1) (hF ab hab).2.2.2
        (haB.trans hpow) (hbB.trans hpow) hgeom
      exact ⟨x, hx, y, hy, hxy, hweak_aligned x hx y hy hxy halign⟩
  have hrest' := hrest.trans (Real.rpow_le_rpow_of_exponent_le hN1
    (by linarith only [] : -3 / 2 + ε / 2 ≤ -41 / 30 + ε / 2))
  have hpart := sum_filter_add_sum_filter_not P (StrongAligned L θ) (infiniteJointMoment L)
  have hfactor : 2 * (N : ℝ) ^ (-41 / 30 + ε / 2) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
    simpa only [show (-41 / 30 + ε / 2) + ε / 2 = -41 / 30 + ε by ring] using hf N (by omega)
  change (∑ T ∈ S, infiniteJointMoment L T) + (∑ T ∈ R, infiniteJointMoment L T) = _ at hpart
  linarith only [hstrong, hrest', hpart, hfactor]

theorem article_14_3 (F : Finset (ℕ × ℕ))
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L F ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨N₀, hN₀, hm⟩ := uniform_mass F hF C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hcrit
  apply hm N hN L hcrit (families N L F)
  intro T hT
  obtain ⟨hTc, hsource⟩ := mem_filter.mp hT
  obtain ⟨hTp, hconn⟩ := mem_filter.mp hTc
  exact ⟨(mem_powersetCard.mp hTp).1, (mem_powersetCard.mp hTp).2, hconn, hsource⟩

end PaperP1.AlignedFamilyTripleMass
