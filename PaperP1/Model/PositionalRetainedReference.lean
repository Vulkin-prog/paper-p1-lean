module

public import PaperP1.Model.PositionalStoppedLaw
public import PaperP1.Probability.PositionalDeficitNorm
public import PaperP1.Probability.PositionalBernoulliProducts

/-! # The exact original retained positional reference and its two deficit costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalRetainedReference

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteConvolutionAlgebra PaperP1.PositionalFiniteLaw PaperP1.PositionalDeficitNorm
  PaperP1.RetainedReferenceIdentity PaperP1.RetainedFamilyEnumeration PaperP1.CompressedJointMoments
  PaperP1.CompletedPositionalLaw

local instance positionalRetainedDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def independent (G : Finset ℕ) (L : ℕ) : FieldLaw ℕ :=
  independentReference G (siteTerm (fun x ↦ infiniteMarginal x L)) 1

def pairs (G : Finset ℕ) (E : Finset (Finset ℕ)) (L : ℕ) : FieldLaw ℕ :=
  pairReference G E (siteTerm (fun x ↦ infiniteMarginal x L))
    (fun I ↦ scalar (infiniteJointMoment L I) * difference I) 1

theorem difference_union (I J : Finset ℕ) (h : Disjoint I J) :
    difference (I ∪ J) = difference I * difference J := prod_union h

theorem admissible_identity (L : ℕ) (hL : 0 < L) (G : Finset ℕ) (E : Finset (Finset ℕ))
    (hcard : ∀ e ∈ E, e.card = 2) (hpos : ∀ e ∈ E, 0 < runRelativeNullity L e)
    (hground : ∀ e ∈ E, e ⊆ G) (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    retainedValue (fun x ↦ squareClassSpace x L) G E
      (fun I ↦ scalar (infiniteJointMoment L I) * difference I) (1 : FieldLaw ℕ) =
      independent G L + pairs G E L -
        directDeficit (fun x ↦ squareClassSpace x L) G (siteTerm (fun x ↦ infiniteMarginal x L)) 1 -
        compressedDeficit (fun x ↦ squareClassSpace x L) G E (siteTerm (fun x ↦ infiniteMarginal x L))
          (fun I ↦ scalar (infiniteJointMoment L I) * difference I) 1 := by
  apply retained_identity (fun x ↦ squareClassSpace x L) G E hcard hpos hground
  · intro I hI
    obtain ⟨hI, hzero⟩ := mem_filter.mp hI
    have hIG := mem_powerset.mp hI
    rw [direct_joint_factor L hL I (fun x hx ↦ hp x (hIG hx)) hzero]
    simp only [siteTerm, prod_mul_distrib, ← map_prod, difference]
  · intro e he A hA
    have hsub := mem_powerset.mp (mem_filter.mp hA).1
    have hcomp := (mem_filter.mp hA).2
    have hUnionG := union_subset (hground e he) (hsub.trans sdiff_subset)
    have hdis := extension_disjoint G e A hsub
    have hprod : (∏ x ∈ A, siteTerm (fun x ↦ infiniteMarginal x L) x) =
        scalar (∏ x ∈ A, infiniteMarginal x L) * difference A := by
      simpa only [familyTerm, one_pow, mul_one] using family_term (fun x ↦ infiniteMarginal x L) A
    rw [compressed_joint_factor L hL e (e ∪ A) (hcard e he) (fun x hx ↦ hp x (hUnionG hx)) hcomp,
      union_sdiff_cancel_left hdis, map_mul, difference_union e A hdis, hprod]
    ring

theorem admissible_norm_bound (L : ℕ) (hL : 0 < L) (G : Finset ℕ) (E : Finset (Finset ℕ))
    (hcard : ∀ e ∈ E, e.card = 2) (hpos : ∀ e ∈ E, 0 < runRelativeNullity L e)
    (hground : ∀ e ∈ E, e ⊆ G) (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    l1Norm (retainedValue (fun x ↦ squareClassSpace x L) G E
      (fun I ↦ scalar (infiniteJointMoment L I) * difference I) (1 : FieldLaw ℕ) -
      (independent G L + pairs G E L)) ≤
        RetainedDeficitNorm.directMass (fun x ↦ squareClassSpace x L) G (fun x ↦ infiniteMarginal x L) +
        RetainedDeficitNorm.compressedMass (fun x ↦ squareClassSpace x L) G E
          (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) := by
  rw [admissible_identity L hL G E hcard hpos hground hp]
  have heq (a b f g : FieldLaw ℕ) : a + b - f - g - (a + b) = -(f + g) := by ring
  rw [heq, l1Norm_neg]
  exact combined_norm_bound (fun x ↦ squareClassSpace x L) G E (fun x ↦ infiniteMarginal x L)
    (infiniteJointMoment L) hcard (fun x hx ↦ (hp x hx).le) (fun e _ ↦ infiniteJointMoment_nonneg L e)

theorem actual_eq_value (H : ℝ) (N L : ℕ) :
    PositionalStoppedLaw.actualReference (RegularStarts.regularStarts N L) L (RetainedGoodEdges.Retained H N L) =
      retainedValue (fun x ↦ squareClassSpace x L) (RegularStarts.regularStarts N L)
        (GoodEdgeCompression.goodEdges H N L) (fun I ↦ scalar (infiniteJointMoment L I) * difference I) (1 : FieldLaw ℕ) := by
  have hsets : retainedSets (RegularStarts.regularStarts N L) (RetainedGoodEdges.Retained H N L) =
      retainedSets (RegularStarts.regularStarts N L)
        (RetainedDependence.Retained (fun x ↦ squareClassSpace x L) (GoodEdgeCompression.goodEdges H N L)) := by
    ext I
    simp only [retainedSets, mem_filter]
    rw [RetainedReferenceTheorem.retained_predicate]
  unfold PositionalStoppedLaw.actualReference retainedValue
  rw [hsets]
  simp only [one_pow, mul_one]

theorem actual_norm_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    l1Norm (PositionalStoppedLaw.actualReference (RegularStarts.regularStarts N L) L
      (RetainedGoodEdges.Retained H N L) -
      (independent (RegularStarts.regularStarts N L) L +
        pairs (RegularStarts.regularStarts N L) (GoodEdgeCompression.goodEdges H N L) L)) ≤
      RetainedReferenceTheorem.firstMass N L + RetainedReferenceTheorem.secondMass H N L := by
  rw [actual_eq_value]
  apply admissible_norm_bound L hL _ _ (RetainedGoodEdges.good_pair_card H N L)
    (fun e he ↦ RetainedGoodEdges.good_pair_positive H N L e he)
    (fun e he ↦ RetainedGoodEdges.good_pair_regular hN e he)
  intro x hx
  rw [RetainedReferenceTheorem.ground_marginal hN hL x hx]
  positivity

theorem scalar_mul_completed (a : ℝ) (ν : FieldLaw ℕ) : ofFinite (scalar a * ν) = a • ofFinite ν := by
  rw [map_mul]
  change algebraMap ℝ (Space ℕ) a * ofFinite ν = a • ofFinite ν
  rw [Algebra.smul_def]

theorem independent_completed (G : Finset ℕ) (L : ℕ) :
    ofFinite (independent G L) = PositionalBernoulliProducts.base G (fun x ↦ infiniteMarginal x L) := by
  unfold independent independentReference PositionalBernoulliProducts.base
  rw [map_prod]
  apply prod_congr rfl
  intro x _
  simp only [siteTerm, mul_one, map_add, map_one, scalar_mul_completed, PositionalBernoulliProducts.site]

theorem pairs_completed (G : Finset ℕ) (E : Finset (Finset ℕ)) (L : ℕ) :
    ofFinite (pairs G E L) = ∑ e ∈ E, infiniteJointMoment L e •
      (ofFinite (difference e) * PositionalBernoulliProducts.base (G \ e) (fun x ↦ infiniteMarginal x L)) := by
  unfold pairs pairReference
  rw [map_sum]
  apply sum_congr rfl
  intro e _
  simp only [one_pow, mul_one, map_mul]
  rw [← independent_completed]
  change (ofFinite (scalar (infiniteJointMoment L e)) * ofFinite (difference e)) *
    ofFinite (independent (G \ e) L) = _
  change (algebraMap ℝ (Space ℕ) (infiniteJointMoment L e) * ofFinite (difference e)) *
    ofFinite (independent (G \ e) L) = _
  rw [mul_assoc, ← Algebra.smul_def]

end PaperP1.PositionalRetainedReference
