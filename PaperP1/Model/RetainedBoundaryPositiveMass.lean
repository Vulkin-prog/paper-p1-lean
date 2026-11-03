module

public import PaperP1.Model.NonretainedPositiveMass
public import PaperP1.Model.RetainedIndependentDeficitComparison
public import PaperP1.Model.RetainedReferenceCardinalityTheorem
public import PaperP1.Model.NongoodPairSeeds

/-! # The exact finite positive-boundary inequality in companion T17.3 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedBoundaryPositiveMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.GoodEdgeCompression PaperP1.RetainedReferenceTheorem PaperP1.ActualComponentRemainder

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (H : ℝ) (N L K : ℕ) : Finset (Finset ℕ) :=
  (RegularStarts.regularStarts N L).powerset.filter fun I ↦
    (runRelativeNullity L I : ℝ) ≤ 3 * L / 2 ∧ ¬RetainedGoodEdges.Retained H N L I ∧ I.card ≤ K

def mass (H : ℝ) (N L K : ℕ) : ℝ :=
  ∑ I ∈ families H N L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I

def goodActivity (H : ℝ) (N L : ℕ) : ℝ := 4 * ∑ e ∈ goodEdges H N L, infiniteCenteredCoefficient L e

def badActivity (H : ℝ) (N L : ℕ) : ℝ :=
  4 * ∑ e ∈ (RegularStarts.regularStarts N L).powersetCard 2 \ goodEdges H N L, |infiniteCenteredCoefficient L e|

def higherActivity (N L K : ℕ) : ℝ :=
  ∑ I ∈ higher (RegularStarts.regularStarts N L) L K (3 / 2), weight L 2 I

theorem good_subset (H : ℝ) (N L : ℕ) (hN : 2 ≤ N) :
    goodEdges H N L ⊆ (RegularStarts.regularStarts N L).powersetCard 2 := by
  intro e he
  exact mem_powersetCard.mpr ⟨RetainedGoodEdges.good_pair_regular hN e he,
    RetainedGoodEdges.good_pair_card H N L e he⟩

theorem good_joint_positive (H : ℝ) (N L : ℕ) (e : Finset ℕ) (he : e ∈ goodEdges H N L) :
    0 < infiniteJointMoment L e := by
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  exact (mem_filter.mp hxy).2.2.2.2.1

theorem good_weight (H : ℝ) (N L : ℕ) (hL : 0 < L) :
    (∑ e ∈ goodEdges H N L, weight L 2 e) = goodActivity H N L := by
  rw [goodActivity, mul_sum]
  apply sum_congr rfl
  intro e he
  have hcard := RetainedGoodEdges.good_pair_card H N L e he
  have hpos := (CenteredSourcePairBound.pointwise L hL e hcard (good_joint_positive H N L e he)).1
  simp only [weight, hcard, abs_of_nonneg hpos]
  norm_num

theorem activities_nonneg (H : ℝ) (N L K : ℕ) (hL : 0 < L) :
    0 ≤ goodActivity H N L ∧ 0 ≤ badActivity H N L ∧ 0 ≤ higherActivity N L K := by
  rw [← good_weight H N L hL]
  exact ⟨sum_nonneg fun e _ ↦ mul_nonneg (by positivity) (abs_nonneg _),
    mul_nonneg (by norm_num) (sum_nonneg fun e _ ↦ abs_nonneg _),
    sum_nonneg fun I _ ↦ mul_nonneg (by positivity) (abs_nonneg _)⟩

theorem pair_activity_split (H : ℝ) (N L : ℕ) (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ e ∈ (RegularStarts.regularStarts N L).powersetCard 2, weight L 2 e) =
      goodActivity H N L + badActivity H N L := by
  have h := sum_sdiff (good_subset H N L hN) (f := weight L 2)
  rw [good_weight H N L hL] at h
  have hbad : (∑ e ∈ (RegularStarts.regularStarts N L).powersetCard 2 \ goodEdges H N L,
      weight L 2 e) = badActivity H N L := by
    rw [badActivity, mul_sum]
    apply sum_congr rfl
    intro e he
    have hcard := (mem_powersetCard.mp (mem_sdiff.mp he).1).2
    simp only [weight, hcard]
    norm_num
  rw [hbad] at h
  linarith only [h]

theorem bad_eq_nongood (H : ℝ) (N L : ℕ) (hL : 0 < L) :
    badActivity H N L = 4 * ∑ e ∈ NongoodPairSeeds.families H N L (RegularStarts.regularStarts N L),
      |infiniteCenteredCoefficient L e| := by
  unfold badActivity
  congr 1
  symm
  apply sum_subset
  · intro e he
    obtain ⟨heG, hecard, _hdep, hnot⟩ := (NongoodPairSeeds.mem_families _ _ _ _ _).mp he
    exact mem_sdiff.mpr ⟨mem_powersetCard.mpr ⟨heG, hecard⟩, hnot⟩
  · intro e he hnot
    obtain ⟨heG, hecard⟩ := mem_powersetCard.mp (mem_sdiff.mp he).1
    have hz : runRelativeNullity L e = 0 := by
      by_contra hn
      exact hnot ((NongoodPairSeeds.mem_families H N L _ e).mpr
        ⟨heG, hecard, Nat.pos_of_ne_zero hn, (mem_sdiff.mp he).2⟩)
    rw [AbsoluteActivityDecomposition.centered_zero_direct L hL e
      (card_pos.mp (by omega)) hz, abs_zero]

theorem finite_bound (H : ℝ) (N L K : ℕ) (hN : 2 ≤ N) (hL : 0 < L) :
    mass H N L K ≤ firstMass N L + secondMass H N L +
      Real.exp (2 * CountObservables.countMoment (RegularStarts.regularStarts N L) L 1) *
        (Real.exp (goodActivity H N L + badActivity H N L + higherActivity N L K) - 1 - goodActivity H N L) := by
  let G := RegularStarts.regularStarts N L
  let E := goodEdges H N L
  let F := families H N L K
  have hdata : ∀ I ∈ F, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ K ∧
      (runRelativeNullity L I : ℝ) ≤ (3 / 2) * L ∧
      ¬RetainedDependence.Retained (fun x ↦ squareClassSpace x L) E I := by
    intro I hI
    obtain ⟨hIG, hcap, hnot, hsize⟩ := mem_filter.mp hI
    have hnr : ¬RetainedDependence.Retained (fun x ↦ squareClassSpace x L) E I :=
      fun hret ↦ hnot ((CompressedBlocks.sourceRetained_iff _ E I).mpr hret)
    have hne : I.Nonempty := by
      by_contra hn
      apply hnr
      rw [not_nonempty_iff_eq_empty.mp hn]
      exact Or.inl (relativeNullityOn_empty _)
    exact ⟨mem_powerset.mp hIG, hne, hsize, by linarith only [hcap], hnr⟩
  have h := NonretainedPositiveMass.finite_bound G L K hL (3 / 2) 2 (by norm_num) E F
    (good_subset H N L hN) (fun e he ↦ good_joint_positive H N L e he) hdata
  have hmean : (∑ x ∈ G, 2 * infiniteMarginal x L) = 2 * CountObservables.countMoment G L 1 := by
    rw [← mul_sum, CountObservables.countMoment_one (RegularStarts.regularStarts_subset N L)]
  have hfirst := RetainedIndependentDeficitComparison.first_eq N L
  have hsecond := RetainedIndependentDeficitComparison.second_eq H N L
  have hactivities := pair_activity_split H N L hN hL
  change mass H N L K ≤ _ at h
  rw [hmean, ← hfirst, hactivities] at h
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  rw [← hsecond] at h
  simpa only [G, E, higherActivity, good_weight H N L hL] using h

end PaperP1.RetainedBoundaryPositiveMass
