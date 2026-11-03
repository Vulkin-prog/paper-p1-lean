module

public import PaperP1.Model.CompressedPairCoefficient
public import PaperP1.Model.AllPairDeficitMonotonicity
public import PaperP1.Combinatorics.DistinguishedPairWeights

/-! # Literal all-cardinality compressed-pair populations, including the distinguished source multiplicity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPairMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PairPrimitiveCompression

def pairs (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (G.powersetCard 2 ×ˢ G.powerset).filter fun p ↦
    0 < runRelativeNullity L p.1 ∧ Primitive L p.1 p.2

def mass (P : Finset (Finset ℕ × Finset ℕ)) (L : ℕ) (u : ℝ) : ℝ :=
  ∑ p ∈ P, u ^ (p.2.card + 2) * (infiniteJointMoment L (p.1 ∪ p.2) +
    |CompressedPairCoefficient.value L p.1 p.2| + |infiniteCenteredCoefficient L (p.1 ∪ p.2)|)

theorem mem_pairs (G : Finset ℕ) (L : ℕ) (p : Finset ℕ × Finset ℕ) :
    p ∈ pairs G L ↔ p.1 ⊆ G ∧ p.1.card = 2 ∧ p.2 ⊆ G ∧
      0 < runRelativeNullity L p.1 ∧ Primitive L p.1 p.2 := by
  classical
  simp only [pairs, mem_filter, mem_product, mem_powersetCard, mem_powerset]
  tauto

theorem mass_nonneg (P : Finset (Finset ℕ × Finset ℕ)) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ mass P L u := sum_nonneg fun _p _ ↦ mul_nonneg (pow_nonneg hu _)
      (add_nonneg (add_nonneg (infiniteJointMoment_nonneg L _) (abs_nonneg _)) (abs_nonneg _))

theorem mass_mono (P Q : Finset (Finset ℕ × Finset ℕ)) (hPQ : P ⊆ Q) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    mass P L u ≤ mass Q L u := sum_le_sum_of_subset_of_nonneg hPQ fun _p _ _ ↦
      mul_nonneg (pow_nonneg hu _) (add_nonneg
        (add_nonneg (infiniteJointMoment_nonneg L _) (abs_nonneg _)) (abs_nonneg _))

theorem join_card (G : Finset ℕ) (L : ℕ) (p : Finset ℕ × Finset ℕ) (hp : p ∈ pairs G L) :
    (p.1 ∪ p.2).card = p.2.card + 2 := by
  obtain ⟨_heG, he, _hAG, _hdep, h⟩ := (mem_pairs G L p).mp hp
  rw [card_union_of_disjoint h.1, he, Nat.add_comm]

theorem target_deficit (G : Finset ℕ) (L : ℕ) (p : Finset ℕ × Finset ℕ) (hp : p ∈ pairs G L) :
    p.2 ∈ IndependentExtensionDeficit.families (G \ p.1) (FixedPairExtensions.sourceSpace p.1 L) L := by
  obtain ⟨_heG, _he, hAG, _hdep, h⟩ := (mem_pairs G L p).mp hp
  let : Fintype (FixedPairExtensions.sourceSpace p.1 L) := MinimalRelativeRelations.spanFintype _ p.1
  apply (IndependentExtensionDeficit.mem_families _ _ _ _).mpr
  refine ⟨fun x hx ↦ mem_sdiff.mpr ⟨hAG hx, fun he ↦ disjoint_left.mp h.1 he hx⟩, ?_⟩
  intro hdirect
  have hz := (IndependentExtensionDeficit.direct_iff_nullity _ _ _).mp hdirect
  have hpos := h.2.2.1
  change nullity L p.1 p.2 = 0 at hz
  omega

theorem source_product_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u) :
    (∑ p ∈ pairs G L, u ^ (p.2.card + 2) *
      (infiniteJointMoment L p.1 * ∏ x ∈ p.2, infiniteMarginal x L)) ≤
        2 * u ^ 2 * AllPairExtensionDeficit.deficit G L u := by
  classical
  let P := pairs G L
  let E := G.powersetCard 2
  let f := fun p : Finset ℕ × Finset ℕ ↦ u ^ (p.2.card + 2) *
    (infiniteJointMoment L p.1 * ∏ x ∈ p.2, infiniteMarginal x L)
  have hsplit := sum_fiberwise_of_maps_to (s := P) (t := E) (g := Prod.fst)
    (fun p hp ↦ mem_powersetCard.mpr ⟨((mem_pairs G L p).mp hp).1, ((mem_pairs G L p).mp hp).2.1⟩) f
  change (∑ p ∈ P, f p) ≤ _
  rw [← hsplit, AllPairExtensionDeficit.deficit, mul_sum]
  apply sum_le_sum
  intro e _he
  let PE := P.filter fun p ↦ p.1 = e
  let F := IndependentExtensionDeficit.families (G \ e) (FixedPairExtensions.sourceSpace e L) L
  have hinj : Set.InjOn Prod.snd (PE : Set (Finset ℕ × Finset ℕ)) := by
    intro p hp q hq heq
    exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) heq
  have hsub : PE.image Prod.snd ⊆ F := by
    intro A hA
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hA
    have h := target_deficit G L p (mem_filter.mp hp).1
    simpa only [(mem_filter.mp hp).2] using h
  have hnonneg (A : Finset ℕ) : 0 ≤ u ^ A.card * ∏ x ∈ A, infiniteMarginal x L :=
    mul_nonneg (pow_nonneg hu _) (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  calc
    _ ≤ ∑ p ∈ PE, 2 * u ^ 2 * |infiniteCenteredCoefficient L e| *
        (u ^ p.2.card * ∏ x ∈ p.2, infiniteMarginal x L) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpP, hpe⟩ := mem_filter.mp hp
      obtain ⟨_heG, hecard, _hAG, hdep, _hprim⟩ := (mem_pairs G L p).mp hpP
      have hq := DependentPairJointActivity.pointwise L hL p.1 hecard hdep
      have hmul := mul_le_mul_of_nonneg_right hq
        (mul_nonneg (pow_nonneg hu (p.2.card + 2))
          (prod_nonneg (s := p.2) fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))
      dsimp only [f]
      rw [hpe] at hmul ⊢
      convert hmul using 1 <;> rw [pow_add] <;> ring
    _ = 2 * u ^ 2 * |infiniteCenteredCoefficient L e| *
        ∑ A ∈ PE.image Prod.snd, u ^ A.card * ∏ x ∈ A, infiniteMarginal x L := by
      rw [sum_image hinj, mul_sum]
    _ ≤ 2 * u ^ 2 * |infiniteCenteredCoefficient L e| *
        IndependentExtensionDeficit.deficit G e (FixedPairExtensions.sourceSpace e L) L u := by
      apply mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ ↦ hnonneg A))
      positivity
    _ = _ := by ring

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u) :
    mass (pairs G L) L u ≤
      2 * (∑ I ∈ (pairs G L).image DistinguishedPairWeights.join,
        (2 * u) ^ I.card * (infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)) +
          2 * u ^ 2 * AllPairExtensionDeficit.deficit G L u := by
  classical
  let P := pairs G L
  let w := fun I ↦ infiniteJointMoment L I + |infiniteCenteredCoefficient L I|
  have hw : ∀ I, 0 ≤ w I := fun I ↦ add_nonneg (infiniteJointMoment_nonneg L I) (abs_nonneg _)
  have hweight := DistinguishedPairWeights.weighted_bound P u hu w hw (fun p hp ↦ ((mem_pairs G L p).mp hp).2.2.2.2.1)
  have hprod := source_product_bound G L hL u hu
  have hpoint : mass P L u ≤
      2 * (∑ p ∈ P, u ^ (DistinguishedPairWeights.join p).card * w (DistinguishedPairWeights.join p)) +
        ∑ p ∈ P, u ^ (p.2.card + 2) * (infiniteJointMoment L p.1 * ∏ x ∈ p.2, infiniteMarginal x L) := by
    rw [mass, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    obtain ⟨_heG, he, _hAG, _hdep, h⟩ := (mem_pairs G L p).mp hp
    have hc := CompressedPairCoefficient.primitive_abs_bound L hL p.1 p.2 he h
    have hmul := mul_le_mul_of_nonneg_left hc (pow_nonneg hu (p.2.card + 2))
    have hnonneg := abs_nonneg (infiniteCenteredCoefficient L (p.1 ∪ p.2))
    dsimp only [DistinguishedPairWeights.join, w]
    rw [join_card G L p hp]
    nlinarith only [hmul, mul_nonneg (pow_nonneg hu (p.2.card + 2)) hnonneg]
  exact hpoint.trans (add_le_add (mul_le_mul_of_nonneg_left hweight (by norm_num)) hprod)

end PaperP1.CompressedPairMass
