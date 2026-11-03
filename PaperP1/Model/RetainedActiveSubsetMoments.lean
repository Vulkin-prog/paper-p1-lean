module

public import PaperP1.Combinatorics.RetainedSubsetCounts
public import PaperP1.Probability.SelectedSubsetCounts
public import PaperP1.Model.ActiveSetCylinder
public import PaperP1.Model.RetainedDeficitGrouping

/-! # Actual direct and compressed-pair subset moments and their exceptional-event leakages -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedActiveSubsetMoments

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.RetainedActiveCount
  PaperP1.RetainedReferenceTheorem PaperP1.RetainedCardinalityDeficits PaperP1.RegularStarts

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def direct (L r : ℕ) (A : Finset ℕ) : ℕ :=
  SelectedSubsetCounts.count (fun I ↦ runRelativeNullity L I = 0) A r

def pair (H : ℝ) (N L r : ℕ) (A : Finset ℕ) : ℕ :=
  RetainedSubsetCounts.pairCount (fun x ↦ squareClassSpace x L) (GoodEdgeCompression.goodEdges H N L) A r

def directMean (N L r : ℕ) : ℝ :=
  ∫ ω, (direct L r (activeSet (regularStarts N L) L ω) : ℝ) ∂infiniteRademacherMeasure

def pairMean (H : ℝ) (N L r : ℕ) : ℝ :=
  ∫ ω, (pair H N L r (activeSet (regularStarts N L) L ω) : ℝ) ∂infiniteRademacherMeasure

def directLeakage (H : ℝ) (N L r : ℕ) : ℝ :=
  ∫ ω, if ¬retainedActive H N L (regularStarts N L) ω then
    (direct L r (activeSet (regularStarts N L) L ω) : ℝ) else 0 ∂infiniteRademacherMeasure

def pairLeakage (H : ℝ) (N L r : ℕ) : ℝ :=
  ∫ ω, if ¬retainedActive H N L (regularStarts N L) ω then
    (pair H N L r (activeSet (regularStarts N L) L ω) : ℝ) else 0 ∂infiniteRademacherMeasure

def modifiedChooseMoment (H : ℝ) (N L r : ℕ) : ℝ :=
  ∫ ω, ((modified H N L (regularStarts N L) ω).choose r : ℝ) ∂infiniteRademacherMeasure

def pairBinomialTerm (H : ℝ) (N L r : ℕ) : ℝ :=
  if r < 2 then 0 else beta H N L * (((regularStarts N L).card - 2).choose (r - 2) : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ (r - 2)

theorem direct_eq_subsets (L r : ℕ) (A : Finset ℕ) :
    direct L r A = RetainedSubsetCounts.directCount (fun x ↦ squareClassSpace x L) A r := by
  unfold direct SelectedSubsetCounts.count RetainedSubsetCounts.directCount
  congr 1

theorem direct_mean {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (r : ℕ) :
    directMean N L r = ((regularStarts N L).card.choose r : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ r - firstCoefficient N L r := by
  let G := regularStarts N L
  let M := MaximumDirectActive.cutoff G L
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  rw [directMean, ActiveSetCylinder.observable_integral G L (fun A ↦ (direct L r A : ℝ))]
  have h := SelectedSubsetCounts.finite_mean (cylinderProbability M) G J
    (fun I ↦ runRelativeNullity L I = 0) r
  change finiteExpectation (cylinderProbability M).weight
    (fun σ ↦ (direct L r (activeSites G J σ) : ℝ)) =
    ∑ I ∈ directAt N L r, finiteJointMoment (cylinderProbability M) J I at h
  rw [h]
  have hsum : (∑ I ∈ directAt N L r, finiteJointMoment (cylinderProbability M) J I) =
      ((directAt N L r).card : ℝ) * ((2 ^ L : ℝ)⁻¹) ^ r := by
    calc
      _ = ∑ _I ∈ directAt N L r, ((2 ^ L : ℝ)⁻¹) ^ r := by
        apply sum_congr rfl
        intro I hI
        obtain ⟨hIG, hz⟩ := mem_filter.mp hI
        obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
        rw [← infiniteJointMoment_eq_finite M L I (fun x hx ↦ le_sup (f := fun y ↦ y + L) (hsub hx)),
          CompressedJointMoments.regular_direct_joint hN hL I hsub hz, hcard]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  rw [hsum, firstCoefficient_real_formula]
  ring

theorem pair_mean_layer {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) (r : ℕ) (hr : 2 ≤ r) :
    pairMean H N L r = ∑ e ∈ GoodEdgeCompression.goodEdges H N L,
      infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (r - 2) * ((gamma N L e (r - 2)).card : ℝ) := by
  let G := regularStarts N L
  let M := MaximumDirectActive.cutoff G L
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  rw [pairMean, ActiveSetCylinder.observable_integral G L (fun A ↦ (pair H N L r A : ℝ))]
  simp only [pair, RetainedSubsetCounts.pairCount, Nat.cast_sum, finiteExpectation_sum]
  apply sum_congr rfl
  intro e he
  have heG := RetainedGoodEdges.good_pair_regular hN e he
  have hecard := RetainedGoodEdges.good_pair_card H N L e he
  have h := SelectedSubsetCounts.finite_mean (cylinderProbability M) G J
    (RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e) r
  change finiteExpectation (cylinderProbability M).weight
    (fun σ ↦ (RetainedSubsetCounts.compressedCount (fun x ↦ squareClassSpace x L) (activeSites G J σ) e r : ℝ)) =
    ∑ I ∈ (G.powersetCard r).filter (RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e),
      finiteJointMoment (cylinderProbability M) J I at h
  rw [h]
  have hfinite : (∑ I ∈ (G.powersetCard r).filter (RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e),
      finiteJointMoment (cylinderProbability M) J I) =
      ∑ I ∈ (G.powersetCard r).filter (RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e), infiniteJointMoment L I := by
    apply sum_congr rfl
    intro I hI
    have hsub := (mem_powersetCard.mp (mem_filter.mp hI).1).1
    exact (infiniteJointMoment_eq_finite M L I (fun x hx ↦ le_sup (f := fun y ↦ y + L) (hsub hx))).symm
  rw [hfinite, RetainedSubsetCounts.compressed_layer_reindex (fun x ↦ squareClassSpace x L) G e heG hecard r hr]
  change (∑ A ∈ gamma N L e (r - 2), infiniteJointMoment L (e ∪ A)) = _
  calc
    _ = ∑ _A ∈ gamma N L e (r - 2), infiniteJointMoment L e * ((2 ^ L : ℝ)⁻¹) ^ (r - 2) := by
      apply sum_congr rfl
      intro A hA
      obtain ⟨hAG, hcomp⟩ := mem_filter.mp hA
      obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hAG
      have hdis := RetainedFamilyEnumeration.extension_disjoint G e A hsub
      have hsize : (e ∪ A).card = r := by rw [card_union_of_disjoint hdis, hecard, hcard]; omega
      rw [CompressedJointMoments.regular_compressed_joint hN hL e (e ∪ A) hecard
        (union_subset heG (hsub.trans sdiff_subset)) hcomp, hsize]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

theorem pair_mean_small (H : ℝ) (N L r : ℕ) (hr : r < 2) : pairMean H N L r = 0 := by
  unfold pairMean pair
  simp only [RetainedSubsetCounts.pairCount_zero_small _ _ (RetainedGoodEdges.good_pair_card H N L) _ r hr,
    Nat.cast_zero, integral_zero]

theorem pair_mean {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) (r : ℕ) :
    pairMean H N L r = pairBinomialTerm H N L r - secondCoefficient H N L r := by
  by_cases hr : r < 2
  · rw [pair_mean_small H N L r hr, pairBinomialTerm, ite_eq_left hr, secondCoefficient_zero_small H N L r hr, sub_zero]
  · have hr2 : 2 ≤ r := by omega
    rw [pair_mean_layer hN hL H r hr2, pairBinomialTerm, ite_eq_right hr, secondCoefficient, beta,
      sum_mul, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro e he
    rw [edgeCoefficient_real_formula hN H e he r hr2]
    ring

end PaperP1.RetainedActiveSubsetMoments
