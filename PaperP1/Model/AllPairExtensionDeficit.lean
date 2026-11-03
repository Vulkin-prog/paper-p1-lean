module

public import PaperP1.Model.PairExtensionSeedTail
public import PaperP1.Model.IndependentExtensionDeficit
public import PaperP1.Combinatorics.AllCardinalitySeedBound
public import PaperP1.Model.FiniteGoodChannelPartition

/-! # Exact all-cardinality pair deficits reduce to finitely many fixed seed sizes and a large relative-seed tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllPairExtensionDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FixedPairExtensions PaperP1.PairExtensionSeedTail PaperP1.FamilyIndependentMass

local instance allPairExtensionDeficitPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def deficit (G : Finset ℕ) (L : ℕ) (u : ℝ) : ℝ :=
  ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| *
    IndependentExtensionDeficit.deficit G e (sourceSpace e L) L u

def classMass (G : Finset ℕ) (L : ℕ) (u : ℝ) (P : Finset (Finset ℕ)) : ℝ :=
  ∑ e ∈ P, |infiniteCenteredCoefficient L e| *
    IndependentExtensionDeficit.deficit G e (sourceSpace e L) L u

def sourceSeeds (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (s : ℕ) : Finset (Finset ℕ) :=
  (Ico 1 s).biUnion (fun k ↦ extensions G L e k) ∪ largeSeeds G L e s

theorem seed_subset (G : Finset ℕ) (L : ℕ) (e A : Finset ℕ) (s : ℕ)
    (hA : A ∈ sourceSeeds G L e s) : A ⊆ G \ e := by
  rcases mem_union.mp hA with hsmall | hlarge
  · obtain ⟨k, _, hk⟩ := mem_biUnion.mp hsmall
    exact ((FixedPairExtensions.mem_extensions G L e A k).mp hk).1
  · exact ((mem_largeSeeds G L e A s).mp hlarge).1

theorem seed_cover (G : Finset ℕ) (L : ℕ) (e U : Finset ℕ) (s : ℕ)
    (hU : U ∈ IndependentExtensionDeficit.families (G \ e) (sourceSpace e L) L) :
    ∃ A ∈ sourceSeeds G L e s, A ⊆ U := by
  classical
  let : Fintype (sourceSpace e L) := MinimalRelativeRelations.spanFintype (fun x ↦ squareClassSpace x L) e
  obtain ⟨hUG, hnot⟩ := (IndependentExtensionDeficit.mem_families _ _ _ _).mp hU
  have hpos : 0 < MinimalRelativeRelations.nullity (sourceSpace e L) (fun x ↦ squareClassSpace x L) U :=
    Nat.pos_of_ne_zero (fun hz ↦ hnot ((IndependentExtensionDeficit.direct_iff_nullity _ _ _).mpr hz))
  obtain ⟨A, hAU, hne, hApos, hproper⟩ :=
    MinimalRelativeRelations.exists_minimal (sourceSpace e L) (fun x ↦ squareClassSpace x L) U hpos
  refine ⟨A, ?_, hAU⟩
  by_cases hsize : A.card < s
  · apply mem_union_left
    apply mem_biUnion.mpr
    refine ⟨A.card, mem_Ico.mpr ⟨hne.card_pos, hsize⟩, ?_⟩
    apply (FixedPairExtensions.mem_extensions G L e A A.card).mpr
    refine ⟨hAU.trans hUG, rfl, ?_⟩
    intro hdirect
    have hcomp := (CompressedBlocks.direct_iff_compressed _ e (e ∪ A) subset_union_left).mp hdirect
    have hdis : Disjoint e A := disjoint_left.mpr (fun x hxE hxA ↦ (mem_sdiff.mp (hUG (hAU hxA))).2 hxE)
    have hz : MinimalRelativeRelations.nullity (sourceSpace e L) (fun x ↦ squareClassSpace x L) A = 0 :=
      (MinimalRelativeRelations.zero_iff_compressed (fun x ↦ squareClassSpace x L) e A hdis).mpr hcomp
    omega
  · apply mem_union_right
    exact (mem_largeSeeds G L e A s).mpr ⟨hAU.trans hUG, by omega,
      RelativeWindowFamilies.minimal_witnesses L (sourceSpace e L) A hApos hproper⟩

theorem one_pair_bound (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (s : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    IndependentExtensionDeficit.deficit G e (sourceSpace e L) L u ≤
      Real.exp (∑ x ∈ G, u * infiniteMarginal x L) *
        ((∑ k ∈ Ico 1 s, u ^ k * independentMass (extensions G L e k) L) +
          ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, u * infiniteMarginal x L) := by
  classical
  let w := fun x ↦ u * infiniteMarginal x L
  have hw : ∀ x, 0 ≤ w x := fun x ↦ mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  rw [IndependentExtensionDeficit.deficit_eq_product_weights]
  have hcover := AllCardinalitySeedBound.cover_bound (G \ e)
    (IndependentExtensionDeficit.families (G \ e) (sourceSpace e L) L) (sourceSeeds G L e s) w hw
    (fun A hA ↦ seed_subset G L e A s hA) (fun U hU ↦
      ⟨((IndependentExtensionDeficit.mem_families _ _ _ _).mp hU).1, seed_cover G L e U s hU⟩)
  have hmass : (∑ A ∈ sourceSeeds G L e s, ∏ x ∈ A, w x) ≤
      (∑ k ∈ Ico 1 s, u ^ k * independentMass (extensions G L e k) L) +
        ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, w x := by
    calc
      _ ≤ (∑ A ∈ (Ico 1 s).biUnion (fun k ↦ extensions G L e k), ∏ x ∈ A, w x) +
          ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, w x :=
        GraphStarWeights.sum_union_le_nonneg ((Ico 1 s).biUnion (fun k ↦ extensions G L e k))
          (largeSeeds G L e s) (fun A ↦ ∏ x ∈ A, w x) (fun A ↦ prod_nonneg fun x _ ↦ hw x)
      _ ≤ (∑ k ∈ Ico 1 s, ∑ A ∈ extensions G L e k, ∏ x ∈ A, w x) +
          ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, w x := add_le_add
        (GraphStarWeights.sum_biUnion_le_nonneg (Ico 1 s) (fun k ↦ extensions G L e k)
          (fun A ↦ ∏ x ∈ A, w x) (fun A ↦ prod_nonneg fun x _ ↦ hw x)) le_rfl
      _ = _ := by
        congr 1
        apply sum_congr rfl
        intro k _
        rw [independentMass, mul_sum]
        apply sum_congr rfl
        intro A hA
        dsimp [w]
        rw [prod_mul_distrib, prod_const, ((FixedPairExtensions.mem_extensions G L e A k).mp hA).2.1]
  have hmean : Real.exp (∑ x ∈ G \ e, w x) ≤ Real.exp (∑ x ∈ G, w x) :=
    Real.exp_le_exp.mpr (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ hw x))
  exact hcover.trans (mul_le_mul hmean hmass (sum_nonneg fun A _ ↦ prod_nonneg fun x _ ↦ hw x) (Real.exp_nonneg _))

theorem class_cap (G : Finset ℕ) (L : ℕ) (u D : ℝ) (P : Finset (Finset ℕ))
    (hcap : ∀ e ∈ P, IndependentExtensionDeficit.deficit G e (sourceSpace e L) L u ≤ D) :
    classMass G L u P ≤ D * CompatibleActivitySplit.absolute L P := by
  calc
    _ ≤ ∑ e ∈ P, |infiniteCenteredCoefficient L e| * D :=
      sum_le_sum (fun e he ↦ mul_le_mul_of_nonneg_left (hcap e he) (abs_nonneg _))
    _ = _ := by rw [← sum_mul, mul_comm]; rfl

theorem class_seed_bound (G : Finset ℕ) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) (s : ℕ)
    (P : Finset (Finset ℕ)) (hP : P ⊆ G.powersetCard 2) :
    classMass G L u P ≤ Real.exp (∑ x ∈ G, u * infiniteMarginal x L) *
      ((∑ k ∈ Ico 1 s, u ^ k * FixedPairExtensions.deficit G L k) +
        ∑ e ∈ P, |infiniteCenteredCoefficient L e| *
          ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, u * infiniteMarginal x L) := by
  classical
  let E := Real.exp (∑ x ∈ G, u * infiniteMarginal x L)
  let f := fun e k ↦ u ^ k * independentMass (extensions G L e k) L
  let g := fun e ↦ ∑ A ∈ largeSeeds G L e s, ∏ x ∈ A, u * infiniteMarginal x L
  have hf : ∀ e k, 0 ≤ f e k := fun e k ↦ mul_nonneg (pow_nonneg hu _)
    (sum_nonneg fun A _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hsmall : (∑ e ∈ P, |infiniteCenteredCoefficient L e| * ∑ k ∈ Ico 1 s, f e k) ≤
      ∑ k ∈ Ico 1 s, u ^ k * FixedPairExtensions.deficit G L k := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_le_sum
    intro k _
    calc
      _ ≤ ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| * f e k :=
        sum_le_sum_of_subset_of_nonneg hP (fun e _ _ ↦ mul_nonneg (abs_nonneg _) (hf e k))
      _ = _ := by
        rw [FixedPairExtensions.deficit, mul_sum]
        apply sum_congr rfl
        intro e _
        dsimp [f]
        ring
  calc
    _ ≤ ∑ e ∈ P, |infiniteCenteredCoefficient L e| * (E * ((∑ k ∈ Ico 1 s, f e k) + g e)) :=
      sum_le_sum (fun e _ ↦ mul_le_mul_of_nonneg_left (one_pair_bound G L e s u hu) (abs_nonneg _))
    _ = E * ((∑ e ∈ P, |infiniteCenteredCoefficient L e| * ∑ k ∈ Ico 1 s, f e k) +
        ∑ e ∈ P, |infiniteCenteredCoefficient L e| * g e) := by
      rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro e _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hsmall le_rfl) (Real.exp_nonneg _)

theorem partition (Q N H L : ℕ) (hL : 0 < L) (u : ℝ) :
    deficit (dyadicBlock N) L u =
      classMass (dyadicBlock N) L u (FiniteGoodChannelPartition.good Q N H L) +
      classMass (dyadicBlock N) L u (FiniteGoodChannelPartition.weak Q N H L) +
      classMass (dyadicBlock N) L u (FiniteGoodChannelPartition.exceptional Q N H L) := by
  classical
  let f := fun e ↦ |infiniteCenteredCoefficient L e| *
    IndependentExtensionDeficit.deficit (dyadicBlock N) e (sourceSpace e L) L u
  have hrestrict : deficit (dyadicBlock N) L u = ∑ e ∈ DependentFamilySeeds.dependentFamilies (dyadicBlock N) L 2, f e := by
    rw [DependentFamilySeeds.dependentFamilies, sum_filter]
    apply sum_congr rfl
    intro e he
    by_cases hpos : 0 < runRelativeNullity L e
    · rw [ite_eq_left hpos]
    · rw [ite_eq_right hpos]
      have hz : runRelativeNullity L e = 0 := Nat.eq_zero_of_not_pos hpos
      have hne : e.Nonempty := card_pos.mp (by have h := (mem_powersetCard.mp he).2; omega)
      rw [AbsoluteActivityDecomposition.centered_zero_direct L hL e hne hz, abs_zero, zero_mul]
  rw [hrestrict, ← FiniteGoodChannelPartition.cover Q N H L]
  have hdis := FiniteGoodChannelPartition.disjoint_classes Q N H L
  rw [sum_union (disjoint_union_left.mpr ⟨hdis.2.1, hdis.2.2⟩), sum_union hdis.1]
  rfl

end PaperP1.AllPairExtensionDeficit
