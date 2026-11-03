module

public import PaperP1.Probability.PositionalFiniteLaw
public import PaperP1.Model.RetainedStoppedLaw

/-! # The original unsigned field and its actual positive stopped boundary

Every configuration coefficient is identified with its event probability
under the original infinite prime-sign model. Positions are never summed out.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalStoppedLaw

open Finset MeasureTheory PaperP1.Algebra PaperP1.Arithmetic PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.Model.InfiniteRademacher PaperP1.PositionalFiniteLaw
  PaperP1.FiniteConvolutionAlgebra PaperP1.Probability.CylinderExpectations
  PaperP1.Probability.InfiniteCylinderTransfer

local instance positionalStoppedLawDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def actualLaw (G : Finset ℕ) (L : ℕ) : FieldLaw ℕ :=
  PositionalFiniteLaw.law G (cylinderProbability (G.sup fun x ↦ x + L)).weight
    (fun x ↦ startIndicator x L)

def actualReference (G : Finset ℕ) (L : ℕ) (D : Finset ℕ → Prop) : FieldLaw ℕ :=
  ∑ I ∈ retainedSets G D, scalar (infiniteJointMoment L I) * difference I

def actualBoundaryKernel (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) : FieldLaw ℕ :=
  boundaryKernel G (cylinderProbability (G.sup fun x ↦ x + L)) (fun x ↦ startIndicator x L) I

theorem configuration_restrict (G : Finset ℕ) (L M : ℕ)
    (hcut : ∀ x ∈ G, x + L ≤ M) (ω : InfiniteSample) :
    configuration G (fun x ↦ startIndicator x L) (restrictToFinite M ω) =
      configuration G (fun x ↦ infiniteStartIndicator x L) ω := by
  unfold configuration
  apply sum_congr rfl
  intro x hx
  change Finsupp.single x (startIndicator x L (restrictToFinite M ω)).toNat =
    Finsupp.single x (infiniteStartIndicator x L ω).toNat
  rw [startIndicator_restrict_eq ω (hcut x hx)]

theorem actualLaw_coeff (G : Finset ℕ) (L : ℕ) (v : Configuration ℕ) :
    (actualLaw G L).coeff v = infiniteRademacherMeasure.real
      {ω | configuration G (fun x ↦ infiniteStartIndicator x L) ω = v} := by
  let M := G.sup fun x ↦ x + L
  have hcut (x : ℕ) (hx : x ∈ G) : x + L ≤ M := le_sup (f := fun x ↦ x + L) hx
  have he : (actualLaw G L).coeff v =
      finiteExpectation (cylinderProbability M).weight
        (fun ω ↦ if configuration G (fun x ↦ startIndicator x L) ω = v then 1 else 0) := by
    unfold actualLaw PositionalFiniteLaw.law
    simp_rw [scalar_mul_atom]
    simp [AddMonoidAlgebra.coeff_sum, Finsupp.single_apply, finiteExpectation, M]
  rw [he, ← infiniteCylinder_event]
  congr 1
  ext ω
  change configuration G (fun x ↦ startIndicator x L) (restrictToFinite M ω) = v ↔
    configuration G (fun x ↦ infiniteStartIndicator x L) ω = v
  rw [configuration_restrict G L M hcut ω]

theorem actualLaw_nonneg (G : Finset ℕ) (L : ℕ) (v : Configuration ℕ) :
    0 ≤ (actualLaw G L).coeff v :=
  PositionalFiniteLaw.law_nonneg G _ _ (cylinderProbability _).weight_nonneg v

theorem actualLaw_mass (G : Finset ℕ) (L : ℕ) : mass (actualLaw G L) = 1 := by
  rw [actualLaw, PositionalFiniteLaw.law_mass]
  exact (cylinderProbability _).total_weight

theorem reference_eq_finite (G : Finset ℕ) (L : ℕ) (D : Finset ℕ → Prop) :
    actualReference G L D = reference G D (cylinderProbability (G.sup fun x ↦ x + L))
      (fun x ↦ startIndicator x L) := by
  apply sum_congr rfl
  intro I hI
  have hIG := mem_powerset.mp (mem_filter.mp hI).1
  rw [← infiniteJointMoment_eq_finite (G.sup fun x ↦ x + L) L I
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) (hIG hx))]

theorem actualBoundaryKernel_nonneg (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (v : Configuration ℕ) :
    0 ≤ (actualBoundaryKernel G L I).coeff v := boundaryKernel_nonneg _ _ _ _ _

theorem actualBoundaryKernel_mass (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (hI : I ⊆ G) :
    mass (actualBoundaryKernel G L I) = infiniteJointMoment L I := by
  rw [actualBoundaryKernel, boundaryKernel_mass]
  exact (infiniteJointMoment_eq_finite (G.sup fun x ↦ x + L) L I
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) (hI hx))).symm

theorem actualBoundaryKernel_l1Norm (G : Finset ℕ) (L : ℕ) (I : Finset ℕ) (hI : I ⊆ G) :
    l1Norm (actualBoundaryKernel G L I) = infiniteJointMoment L I :=
  (l1Norm_eq_mass_of_nonneg _ (actualBoundaryKernel_nonneg G L I)).trans
    (actualBoundaryKernel_mass G L I hI)

theorem stopped_difference (G : Finset ℕ) (L : ℕ) (D : Finset ℕ → Prop)
    (hD : Hereditary D) (h_empty : D ∅) :
    actualLaw G L - actualReference G L D =
      ∑ I ∈ boundarySets G D, difference I * actualBoundaryKernel G L I := by
  rw [reference_eq_finite]
  exact PositionalFiniteLaw.stopped_difference G D _ _ hD h_empty

theorem stopped_l1_bound (G : Finset ℕ) (L : ℕ) (D : Finset ℕ → Prop)
    (hD : Hereditary D) (h_empty : D ∅) :
    l1Norm (actualLaw G L - actualReference G L D) ≤
      ∑ I ∈ boundarySets G D, (2 : ℝ) ^ I.card * infiniteJointMoment L I := by
  rw [reference_eq_finite]
  have hh := PositionalFiniteLaw.stopped_l1_bound G D (cylinderProbability (G.sup fun x ↦ x + L))
    (fun x ↦ startIndicator x L) hD h_empty
  apply hh.trans_eq
  apply sum_congr rfl
  intro I hI
  have hIG := mem_powerset.mp (mem_filter.mp hI).1
  rw [← infiniteJointMoment_eq_finite (G.sup fun x ↦ x + L) L I
    (fun x hx ↦ le_sup (f := fun x ↦ x + L) (hIG hx))]

theorem boundary_bound (H : ℝ) (N L K : ℕ) (hN : 2 ≤ N) (hL : 7 ≤ L) :
    l1Norm (actualLaw (RegularStarts.regularStarts N L) L -
      actualReference (RegularStarts.regularStarts N L) L (RetainedGoodEdges.Retained H N L)) ≤
      RetainedBoundaryPositiveMass.mass H N L K + LargeBoundaryMass.mass H N L K := by
  let G := RegularStarts.regularStarts N L
  let D := RetainedGoodEdges.Retained H N L
  let B := boundarySets G D
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
    simp only [B, G, D, P, boundarySets, LargeBoundaryMass.families, mem_filter, not_le]
    tauto
  have hsplit := sum_filter_add_sum_filter_not B P (fun I ↦ (2 : ℝ) ^ I.card * infiniteJointMoment L I)
  rw [hlarge] at hsplit
  have hbound := stopped_l1_bound G L D (RetainedGoodEdges.hereditary H N L)
    (RetainedActiveCount.retained_empty H N L)
  change (∑ I ∈ B.filter P, (2 : ℝ) ^ I.card * infiniteJointMoment L I) ≤ RetainedBoundaryPositiveMass.mass H N L K at hsmall
  change l1Norm _ ≤ ∑ I ∈ B, (2 : ℝ) ^ I.card * infiniteJointMoment L I at hbound
  change l1Norm _ ≤ RetainedBoundaryPositiveMass.mass H N L K +
    (∑ I ∈ LargeBoundaryMass.families H N L K, (2 : ℝ) ^ I.card * infiniteJointMoment L I)
  linarith only [hsmall, hsplit, hbound]

end PaperP1.PositionalStoppedLaw
