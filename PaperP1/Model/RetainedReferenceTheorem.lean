module

public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Probability.RetainedDeficitNorm

/-! # The actual retained reference and its exact finite binomial correction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedReferenceTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.Model
  PaperP1.Model.InfiniteStarts PaperP1.RegularStarts PaperP1.GoodEdgeCompression
  PaperP1.RetainedGoodEdges PaperP1.CompressedJointMoments PaperP1.RetainedReferenceIdentity
  PaperP1.RetainedDeficitNorm PaperP1.RetainedFamilyEnumeration

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def actualReference (H : ℝ) (N L : ℕ) : SignedLaw ℝ :=
  ∑ I ∈ retainedSets (regularStarts N L) (RetainedGoodEdges.Retained H N L),
    scalar (infiniteJointMoment L I) * forwardDifference ^ I.card

def beta (H : ℝ) (N L : ℕ) : ℝ := ∑ e ∈ goodEdges H N L, infiniteJointMoment L e

def binomialReference (H : ℝ) (N L : ℕ) : SignedLaw ℝ :=
  bernoulli ((2 ^ L : ℝ)⁻¹) ^ (regularStarts N L).card +
    scalar (beta H N L) * forwardDifference ^ 2 * bernoulli ((2 ^ L : ℝ)⁻¹) ^ ((regularStarts N L).card - 2)

def firstDeficit (N L : ℕ) : SignedLaw ℝ :=
  directDeficit (fun x ↦ squareClassSpace x L) (regularStarts N L)
    (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference

def secondDeficit (H : ℝ) (N L : ℕ) : SignedLaw ℝ :=
  compressedDeficit (fun x ↦ squareClassSpace x L) (regularStarts N L) (goodEdges H N L)
    (fun x ↦ scalar (infiniteMarginal x L)) (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference

def firstMass (N L : ℕ) : ℝ :=
  directMass (fun x ↦ squareClassSpace x L) (regularStarts N L) (fun x ↦ infiniteMarginal x L)

def secondMass (H : ℝ) (N L : ℕ) : ℝ :=
  compressedMass (fun x ↦ squareClassSpace x L) (regularStarts N L) (goodEdges H N L)
    (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)

theorem retained_predicate (H : ℝ) (N L : ℕ) (I : Finset ℕ) :
    RetainedGoodEdges.Retained H N L I ↔
      RetainedDependence.Retained (fun x ↦ squareClassSpace x L) (goodEdges H N L) I :=
  CompressedBlocks.sourceRetained_iff _ _ I

theorem actualReference_eq_value (H : ℝ) (N L : ℕ) :
    actualReference H N L = retainedValue (fun x ↦ squareClassSpace x L) (regularStarts N L)
      (goodEdges H N L) (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference := by
  have hsets : retainedSets (regularStarts N L) (RetainedGoodEdges.Retained H N L) =
      retainedSets (regularStarts N L) (RetainedDependence.Retained (fun x ↦ squareClassSpace x L) (goodEdges H N L)) := by
    ext I
    simp only [retainedSets, mem_filter]
    rw [retained_predicate]
  unfold actualReference retainedValue
  rw [hsets]

theorem ground_marginal {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (x : ℕ) (hx : x ∈ regularStarts N L) :
    infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ := by
  have hxN := (mem_Ico.mp (mem_regularStarts.mp hx).1).1
  exact marginal_on_regular (by omega) hL hx

theorem admissible_identity (L : ℕ) (hL : 0 < L) (G : Finset ℕ) (E : Finset (Finset ℕ))
    (hcard : ∀ e ∈ E, e.card = 2)
    (hpos : ∀ e ∈ E, 0 < relativeNullityOn (fun x ↦ squareClassSpace x L) e)
    (hground : ∀ e ∈ E, e ⊆ G) (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    retainedValue (fun x ↦ squareClassSpace x L) G E (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference =
      independentReference G (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference +
      pairReference G E (fun x ↦ scalar (infiniteMarginal x L)) (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference -
      directDeficit (fun x ↦ squareClassSpace x L) G (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference -
      compressedDeficit (fun x ↦ squareClassSpace x L) G E (fun x ↦ scalar (infiniteMarginal x L))
        (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference := by
  classical
  apply retained_identity (fun x ↦ squareClassSpace x L) G E hcard hpos hground
  · intro I hI
    obtain ⟨hI, hzero⟩ := mem_filter.mp hI
    have hIG := mem_powerset.mp hI
    rw [direct_joint_factor L hL I (fun x hx ↦ hp x (hIG hx)) hzero, map_prod]
  · intro e he A hA
    have hsub := mem_powerset.mp (mem_filter.mp hA).1
    have hcomp := (mem_filter.mp hA).2
    have hUnionG := union_subset (hground e he) (hsub.trans sdiff_subset)
    have hdis := extension_disjoint G e A hsub
    rw [compressed_joint_factor L hL e (e ∪ A) (hcard e he) (fun x hx ↦ hp x (hUnionG hx)) hcomp,
      union_sdiff_cancel_left hdis, map_mul, map_prod]

theorem admissible_norm_bound (L : ℕ) (hL : 0 < L) (G : Finset ℕ) (E : Finset (Finset ℕ))
    (hcard : ∀ e ∈ E, e.card = 2)
    (hpos : ∀ e ∈ E, 0 < relativeNullityOn (fun x ↦ squareClassSpace x L) e)
    (hground : ∀ e ∈ E, e ⊆ G) (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    l1Norm (retainedValue (fun x ↦ squareClassSpace x L) G E (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference -
      (independentReference G (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference +
        pairReference G E (fun x ↦ scalar (infiniteMarginal x L))
          (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference)) ≤
      directMass (fun x ↦ squareClassSpace x L) G (fun x ↦ infiniteMarginal x L) +
        compressedMass (fun x ↦ squareClassSpace x L) G E (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) := by
  rw [admissible_identity L hL G E hcard hpos hground hp]
  have heq (a b f g : SignedLaw ℝ) : a + b - f - g - (a + b) = -(f + g) := by ring1
  rw [heq, l1Norm_neg]
  exact combined_norm_le (fun x ↦ squareClassSpace x L) G E (fun x ↦ infiniteMarginal x L)
    (infiniteJointMoment L) (fun x hx ↦ (hp x hx).le) (fun e _he ↦ infiniteJointMoment_nonneg L e)

theorem heterogeneous_identity {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    actualReference H N L =
      independentReference (regularStarts N L) (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference +
      pairReference (regularStarts N L) (goodEdges H N L) (fun x ↦ scalar (infiniteMarginal x L))
        (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference - firstDeficit N L - secondDeficit H N L := by
  rw [actualReference_eq_value]
  unfold firstDeficit secondDeficit
  exact admissible_identity L hL (regularStarts N L) (goodEdges H N L) (good_pair_card H N L)
    (fun e he ↦ good_pair_positive H N L e he) (fun e he ↦ good_pair_regular hN e he)
    (fun x hx ↦ by rw [ground_marginal hN hL x hx]; positivity)

theorem independentReference_eq_binomial {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (A : Finset ℕ) (hA : A ⊆ regularStarts N L) :
    independentReference A (fun x ↦ scalar (infiniteMarginal x L)) forwardDifference =
      bernoulli ((2 ^ L : ℝ)⁻¹) ^ A.card := by
  unfold independentReference
  calc
    _ = ∏ _x ∈ A, bernoulli ((2 ^ L : ℝ)⁻¹) := by
      apply prod_congr rfl
      intro x hx
      dsimp only
      rw [ground_marginal hN hL x (hA hx)]
      rfl
    _ = _ := by simp

theorem pairReference_eq_binomial {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    pairReference (regularStarts N L) (goodEdges H N L) (fun x ↦ scalar (infiniteMarginal x L))
      (fun I ↦ scalar (infiniteJointMoment L I)) forwardDifference =
        scalar (beta H N L) * forwardDifference ^ 2 *
          bernoulli ((2 ^ L : ℝ)⁻¹) ^ ((regularStarts N L).card - 2) := by
  unfold pairReference
  calc
    _ = ∑ e ∈ goodEdges H N L, scalar (infiniteJointMoment L e) * forwardDifference ^ 2 *
        bernoulli ((2 ^ L : ℝ)⁻¹) ^ ((regularStarts N L).card - 2) := by
      apply sum_congr rfl
      intro e he
      rw [independentReference_eq_binomial hN hL _ sdiff_subset,
        card_sdiff_of_subset (good_pair_regular hN e he), good_pair_card H N L e he]
    _ = _ := by simp only [beta, map_sum, sum_mul]

theorem finite_identity {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    actualReference H N L = binomialReference H N L - firstDeficit N L - secondDeficit H N L := by
  rw [heterogeneous_identity hN hL H, independentReference_eq_binomial hN hL _ (Subset.refl _),
    pairReference_eq_binomial hN hL H]
  rfl

theorem finite_norm_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (H : ℝ) :
    l1Norm (actualReference H N L - binomialReference H N L) ≤ firstMass N L + secondMass H N L := by
  have heq : actualReference H N L - binomialReference H N L = -(firstDeficit N L + secondDeficit H N L) := by
    rw [finite_identity hN hL H]
    ring1
  rw [heq, l1Norm_neg]
  exact combined_norm_le (fun x ↦ squareClassSpace x L) (regularStarts N L) (goodEdges H N L)
    (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L)
    (fun x _hx ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (fun e _he ↦ infiniteJointMoment_nonneg L e)

end PaperP1.RetainedReferenceTheorem
