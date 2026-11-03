module

public import PaperP1.Model.NongoodPairSeeds
public import PaperP1.Model.TwoDependentPairSeeds
public import PaperP1.Model.CompressedPairMass
public import PaperP1.Model.PrimitiveActiveSeeds
public import PaperP1.Model.WeightedPrimitiveMass
public import PaperP1.Model.ActiveEdgeObservables

/-! # An exhaustive positive seed cover of the literal nonretained active event, at every cardinality -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedActivationSeeds

open Finset MeasureTheory PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Model.InfiniteRademacher PaperP1.RetainedActiveCount PaperP1.RetainedCountCylinder
  PaperP1.ConnectedWindowFamilies PaperP1.GoodEdgeCompression

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (H : ℝ) (N L : ℕ) (G : Finset ℕ) : Finset (Finset ℕ) :=
  ((NongoodPairSeeds.families H N L G ∪ WeightedPrimitiveMass.families G L 3) ∪
    TwoDependentPairSeeds.families G L) ∪ (CompressedPairMass.pairs G L).image DistinguishedPairWeights.join

theorem family_subset (H : ℝ) (N L : ℕ) (G I : Finset ℕ) (hI : I ∈ families H N L G) : I ⊆ G := by
  rcases mem_union.mp hI with hI | hcomp
  · rcases mem_union.mp hI with hI | htwo
    · rcases mem_union.mp hI with hbad | hprim
      · exact ((NongoodPairSeeds.mem_families H N L G I).mp hbad).1
      · exact ((WeightedPrimitiveMass.mem_families G I L 3).mp hprim).1
    · exact (TwoDependentPairSeeds.family_data G L I htwo).1
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp hcomp
    have hd := (CompressedPairMass.mem_pairs G L p).mp hp
    exact union_subset hd.1 hd.2.2.1

theorem primitive_seed (H : ℝ) (N L : ℕ) (G I : Finset ℕ) (hIG : I ⊆ G)
    (hthree : 3 ≤ I.card) (hprim : Primitive L I) : I ∈ families H N L G :=
  mem_union_left _ (mem_union_left _ (mem_union_right _ ((WeightedPrimitiveMass.mem_families G I L 3).mpr
    ⟨hIG, hthree, hprim⟩)))

theorem cover (H : ℝ) (N L : ℕ) (G I : Finset ℕ) (hIG : I ⊆ G)
    (hnot : ¬RetainedGoodEdges.Retained H N L I) : ∃ D ∈ families H N L G, D ⊆ I := by
  classical
  obtain ⟨e, heI, hprim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L I
    (PrimitiveActiveSeeds.not_retained_positive H N L I hnot)
  have heG := heI.trans hIG
  have htwo := PrimitiveActiveSeeds.primitive_card_ge_two L e hprim
  by_cases hecard : e.card = 2
  · by_cases hgood : e ∈ goodEdges H N L
    · let S := fun x ↦ squareClassSpace x L
      let W := FixedPairExtensions.sourceSpace e L
      let : Fintype W := MinimalRelativeRelations.spanFintype S e
      have hdis : Disjoint e (I \ e) := disjoint_left.mpr fun x he hx ↦ (mem_sdiff.mp hx).2 he
      have hpos : 0 < MinimalRelativeRelations.nullity W S (I \ e) := by
        apply Nat.pos_of_ne_zero
        intro hz
        have hcomp := (MinimalRelativeRelations.zero_iff_compressed S e (I \ e) hdis).mp hz
        rw [union_sdiff_of_subset heI] at hcomp
        apply hnot
        apply (CompressedBlocks.sourceRetained_iff S (goodEdges H N L) I).mpr
        exact Or.inr ⟨e, hgood, hcomp⟩
      obtain ⟨A, hAI, _hne, hApos, hproper⟩ := MinimalRelativeRelations.exists_minimal W S (I \ e) hpos
      have hAG : A ⊆ G := hAI.trans (sdiff_subset.trans hIG)
      have heA : Disjoint e A := hdis.mono_right hAI
      by_cases hzero : runRelativeNullity L A = 0
      · have hcompressed : PairPrimitiveCompression.Primitive L e A := ⟨heA, hzero, hApos, hproper⟩
        have hp : (e, A) ∈ CompressedPairMass.pairs G L := (CompressedPairMass.mem_pairs G L (e, A)).mpr
          ⟨heG, hecard, hAG, hprim.1, hcompressed⟩
        exact ⟨e ∪ A, mem_union_right _ (mem_image.mpr ⟨(e, A), hp, rfl⟩),
          union_subset heI (hAI.trans sdiff_subset)⟩
      · obtain ⟨f, hfA, hfprim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L A (Nat.pos_of_ne_zero hzero)
        have hfI := hfA.trans (hAI.trans sdiff_subset)
        have hfG := hfI.trans hIG
        have hftwo := PrimitiveActiveSeeds.primitive_card_ge_two L f hfprim
        by_cases hfcard : f.card = 2
        · have hef : Disjoint e f := heA.mono_right hfA
          have hp : (e, f) ∈ TwoDependentPairSeeds.sourcePairs G L :=
            (TwoDependentPairSeeds.mem_sourcePairs G L (e, f)).mpr
              ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨heG, hecard⟩, hprim.1⟩,
                mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hfG, hfcard⟩, hfprim.1⟩, hef⟩
          exact ⟨e ∪ f, mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(e, f), hp, rfl⟩)),
            union_subset heI hfI⟩
        · exact ⟨f, primitive_seed H N L G f hfG (by omega) hfprim, hfI⟩
    · have heBad := (NongoodPairSeeds.mem_families H N L G e).mpr ⟨heG, hecard, hprim.1, hgood⟩
      exact ⟨e, mem_union_left _ (mem_union_left _ (mem_union_left _ heBad)), heI⟩
  · exact ⟨e, primitive_seed H N L G e heG (by omega) hprim, heI⟩

theorem compressed_joint_bound (G : Finset ℕ) (L : ℕ) :
    (∑ I ∈ (CompressedPairMass.pairs G L).image DistinguishedPairWeights.join, infiniteJointMoment L I) ≤
      CompressedPairMass.mass (CompressedPairMass.pairs G L) L 1 := by
  calc
    _ ≤ ∑ p ∈ CompressedPairMass.pairs G L, infiniteJointMoment L (p.1 ∪ p.2) :=
      sum_image_le_of_nonneg (fun I _ ↦ infiniteJointMoment_nonneg L I)
    _ ≤ _ := by
      apply sum_le_sum
      intro p _hp
      simp only [one_pow, one_mul]
      have h1 := abs_nonneg (CompressedPairCoefficient.value L p.1 p.2)
      have h2 := abs_nonneg (infiniteCenteredCoefficient L (p.1 ∪ p.2))
      linarith only [h1, h2]

theorem joint_bound (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    (∑ I ∈ families H N L G, infiniteJointMoment L I) ≤
      (∑ e ∈ NongoodPairSeeds.families H N L G, infiniteJointMoment L e) +
      (∑ I ∈ WeightedPrimitiveMass.families G L 3, infiniteJointMoment L I) +
      (∑ I ∈ TwoDependentPairSeeds.families G L, infiniteJointMoment L I) +
        CompressedPairMass.mass (CompressedPairMass.pairs G L) L 1 := by
  have h1 := GraphStarWeights.sum_union_le_nonneg (NongoodPairSeeds.families H N L G)
    (WeightedPrimitiveMass.families G L 3) (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h2 := GraphStarWeights.sum_union_le_nonneg
    (NongoodPairSeeds.families H N L G ∪ WeightedPrimitiveMass.families G L 3)
    (TwoDependentPairSeeds.families G L) (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h3 := GraphStarWeights.sum_union_le_nonneg
    ((NongoodPairSeeds.families H N L G ∪ WeightedPrimitiveMass.families G L 3) ∪ TwoDependentPairSeeds.families G L)
    ((CompressedPairMass.pairs G L).image DistinguishedPairWeights.join) (infiniteJointMoment L) (infiniteJointMoment_nonneg L)
  have h4 := compressed_joint_bound G L
  change (∑ I ∈ ((NongoodPairSeeds.families H N L G ∪ WeightedPrimitiveMass.families G L 3) ∪
    TwoDependentPairSeeds.families G L) ∪ (CompressedPairMass.pairs G L).image DistinguishedPairWeights.join,
    infiniteJointMoment L I) ≤ _
  linarith only [h1, h2, h3, h4]

theorem badProbability_le_mass (H : ℝ) (N L : ℕ) (G : Finset ℕ) :
    badProbability H N L G ≤ ∑ I ∈ families H N L G, infiniteJointMoment L I := by
  have hsub : {ω | ¬retainedActive H N L G ω} ⊆
      {ω | 0 < ActiveEdgeObservables.value (families H N L G) L ω} := by
    intro ω hω
    obtain ⟨D, hD, hDA⟩ := cover H N L G (activeSet G L ω) (filter_subset _ _) hω
    apply (ActiveEdgeObservables.positive_iff _ L ω).mpr
    exact ⟨D, hD, fun x hx ↦ (mem_filter.mp (hDA hx)).2⟩
  have hprob : badProbability H N L G ≤ ActiveEdgeObservables.probability (families H N L G) L :=
    measureReal_mono hsub
  exact hprob.trans (ActiveEdgeObservables.probability_le_mass (M := MaximumDirectActive.cutoff G L) _ (by
    intro I hI x hx
    exact le_sup (f := fun x ↦ x + L) (family_subset H N L G I hI hx)))

end PaperP1.RetainedActivationSeeds
