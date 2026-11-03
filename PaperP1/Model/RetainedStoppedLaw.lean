module

public import PaperP1.Model.RetainedBoundaryPositiveMass
public import PaperP1.Model.LargeBoundaryMass
public import PaperP1.Model.OriginalCountLawCoupling
public import PaperP1.Model.RetainedActiveCount
public import PaperP1.Probability.SignedAtomicDistance

/-! # The original actual count law, the stopped retained reference and the exact small/large positive boundary split -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedStoppedLaw

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.RetainedReferenceTheorem

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_law_embedding {Ω ι : Type*} [Fintype Ω] [LinearOrder ι]
    (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) :
    (FiniteObservationLaw.law P (indicatorCount G J) : Measure ℕ).toSignedMeasure =
      FiniteLawEmbedding.embed (countLaw G P.weight J) := by
  rw [countLaw_eq_observationLaw]
  apply AtomicSignedLaw.signedMeasure_ext_singleton
  intro k
  rw [Measure.toSignedMeasure_apply_measurable (measurableSet_singleton k), FiniteLawEmbedding.embed_singleton]
  exact FiniteObservationLaw.realMass_eq_coeff P (indicatorCount G J) k

theorem finite_count_bound (H : ℝ) (N L : ℕ) :
    SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (RegularStarts.regularStarts N L) L : Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (actualReference H N L)) ≤
      ∑ I ∈ boundarySets (RegularStarts.regularStarts N L) (RetainedGoodEdges.Retained H N L),
        (2 : ℝ) ^ I.card * infiniteJointMoment L I := by
  classical
  let G := RegularStarts.regularStarts N L
  let M := MaximumDirectActive.cutoff G L
  let J : ℕ → SampleSpace M → Bool := fun x ↦ startIndicator x L
  let D := RetainedGoodEdges.Retained H N L
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have href : retainedCountReference G D (cylinderProbability M) J = actualReference H N L := by
    apply sum_congr rfl
    intro I hI
    have hIG := mem_powerset.mp (mem_filter.mp hI).1
    rw [← infiniteJointMoment_eq_finite M L I (fun x hx ↦ hcut x (hIG hx))]
  have hstop := stopped_finite_count_l1_bound G D (cylinderProbability M) J
    (RetainedGoodEdges.hereditary H N L) (RetainedActiveCount.retained_empty H N L)
  rw [href] at hstop
  have hlaw : (RetainedModifiedLaw.originalLaw G L : Measure ℕ).toSignedMeasure =
      FiniteLawEmbedding.embed (countLaw G (cylinderProbability M).weight J) := by
    rw [← OriginalCountLawCoupling.finite_law M L G hcut]
    exact finite_law_embedding G (cylinderProbability M) J
  rw [hlaw, SignedAtomicDistance.finite_eq]
  apply hstop.trans_eq
  apply sum_congr rfl
  intro I hI
  have hIG := mem_powerset.mp (mem_filter.mp hI).1
  rw [← infiniteJointMoment_eq_finite M L I (fun x hx ↦ hcut x (hIG hx))]

theorem boundary_bound (H : ℝ) (N L K : ℕ) (hN : 2 ≤ N) (hL : 7 ≤ L) :
    SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (RegularStarts.regularStarts N L) L : Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (actualReference H N L)) ≤
      RetainedBoundaryPositiveMass.mass H N L K + LargeBoundaryMass.mass H N L K := by
  classical
  let B := boundarySets (RegularStarts.regularStarts N L) (RetainedGoodEdges.Retained H N L)
  let P := fun I : Finset ℕ ↦ I.card ≤ K
  have hsmallsub : B.filter P ⊆ RetainedBoundaryPositiveMass.families H N L K := by
    intro I hI
    obtain ⟨hIB, hsize⟩ := mem_filter.mp hI
    obtain ⟨hIG, hboundary⟩ := mem_filter.mp hIB
    have hreg := mem_powerset.mp hIG
    have hrank := (RetainedGoodEdges.finite_boundary_bound hN hL I hreg hboundary).2.2.le
    exact mem_filter.mpr ⟨hIG, hrank, hboundary.1, hsize⟩
  have hsmall := sum_le_sum_of_subset_of_nonneg hsmallsub (fun I _ _ ↦
    mul_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ I.card) (infiniteJointMoment_nonneg L I))
  have hlarge : B.filter (fun I ↦ ¬ P I) = LargeBoundaryMass.families H N L K := by
    ext I
    simp only [B, P, boundarySets, LargeBoundaryMass.families, mem_filter, not_le]
    tauto
  have hsplit := sum_filter_add_sum_filter_not B P (fun I ↦ (2 : ℝ) ^ I.card * infiniteJointMoment L I)
  rw [hlarge] at hsplit
  have hbound := finite_count_bound H N L
  change SignedAtomicDistance.distance _ _ ≤ RetainedBoundaryPositiveMass.mass H N L K +
    (∑ I ∈ LargeBoundaryMass.families H N L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I)
  change (∑ I ∈ B.filter P, (2 : ℝ) ^ I.card * infiniteJointMoment L I) ≤ RetainedBoundaryPositiveMass.mass H N L K at hsmall
  change SignedAtomicDistance.distance _ _ ≤ ∑ I ∈ B, (2 : ℝ) ^ I.card * infiniteJointMoment L I at hbound
  linarith only [hsmall, hsplit, hbound]

theorem binomial_bound (H : ℝ) (N L K : ℕ) (hN : 2 ≤ N) (hL : 7 ≤ L) :
    SignedAtomicDistance.distance
      (RetainedModifiedLaw.originalLaw (RegularStarts.regularStarts N L) L : Measure ℕ).toSignedMeasure
      (FiniteLawEmbedding.embed (binomialReference H N L)) ≤
      (RetainedBoundaryPositiveMass.mass H N L K + LargeBoundaryMass.mass H N L K) +
        (firstMass N L + secondMass H N L) := by
  have href := finite_norm_bound hN (by omega : 0 < L) H
  rw [← SignedAtomicDistance.finite_eq] at href
  exact (SignedAtomicDistance.triangle _ (FiniteLawEmbedding.embed (actualReference H N L)) _).trans
    (add_le_add (boundary_bound H N L K hN hL) href)

end PaperP1.RetainedStoppedLaw
