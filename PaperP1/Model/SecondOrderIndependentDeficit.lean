module

public import PaperP1.Model.SecondOrderRetainedClass
public import PaperP1.Model.AllPairExtensionDeficit
public import PaperP1.Model.ActualComponentRemainder
public import PaperP1.Combinatorics.SeedComplementSum
public import PaperP1.Combinatorics.RestrictedSeedComplements

/-! # The independent mass discarded by the all-pair class is charged to larger primitives and failed pair extensions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondOrderIndependentDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SecondOrderRetainedClass PaperP1.ActualComponentRemainder

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def primitives (G : Finset ℕ) (L : ℕ) : Finset (Finset ℕ) :=
  G.powerset.filter fun D ↦ 3 ≤ D.card ∧ ConnectedWindowFamilies.Primitive L D

theorem failed_complement (G : Finset ℕ) (L : ℕ) (I e : Finset ℕ) (hIG : I ⊆ G)
    (hnot : ¬Retained G L I) (he : e ∈ G.powersetCard 2) (heI : e ⊆ I) :
    I \ e ∈ IndependentExtensionDeficit.families (G \ e) (FixedPairExtensions.sourceSpace e L) L := by
  let S := fun x ↦ squareClassSpace x L
  let W := FixedPairExtensions.sourceSpace e L
  let : Fintype W := MinimalRelativeRelations.spanFintype S e
  refine (IndependentExtensionDeficit.mem_families _ _ _ _).mpr ⟨sdiff_subset_sdiff_left e hIG, ?_⟩
  intro hdirect
  have hz := (IndependentExtensionDeficit.direct_iff_nullity W L (I \ e)).mp hdirect
  have hdis : Disjoint e (I \ e) := disjoint_left.mpr fun x hx he ↦ (mem_sdiff.mp he).2 hx
  have hcomp := (MinimalRelativeRelations.zero_iff_compressed S e (I \ e) hdis).mp hz
  rw [union_sdiff_of_subset heI] at hcomp
  exact hnot (Or.inr ⟨e, he, hcomp⟩)

theorem pair_bound (G : Finset ℕ) (L : ℕ) (u : ℝ) (hu : 0 ≤ u) (F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ ¬Retained G L I) :
    (∑ I ∈ F, ∑ e ∈ G.powersetCard 2, if e ⊆ I then u ^ 2 * |infiniteCenteredCoefficient L e| *
      ∏ x ∈ I \ e, u * infiniteMarginal x L else 0) ≤
      u ^ 2 * AllPairExtensionDeficit.deficit G L u := by
  classical
  let w := fun x ↦ u * infiniteMarginal x L
  have hw (x : ℕ) : 0 ≤ w x := mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  rw [sum_comm, AllPairExtensionDeficit.deficit, mul_sum]
  apply sum_le_sum
  intro e he
  let FE := F.filter fun I ↦ e ⊆ I
  have hfiber : (∑ I ∈ FE, ∏ x ∈ I \ e, w x) ≤
      ∑ A ∈ IndependentExtensionDeficit.families (G \ e) (FixedPairExtensions.sourceSpace e L) L, ∏ x ∈ A, w x := by
    apply RestrictedSeedComplements.fiber_bound FE e _ w hw
    intro I hI
    obtain ⟨hIF, heI⟩ := mem_filter.mp hI
    exact ⟨heI, failed_complement G L I e (hF I hIF).1 (hF I hIF).2 he heI⟩
  calc
    _ = (u ^ 2 * |infiniteCenteredCoefficient L e|) * ∑ I ∈ FE, ∏ x ∈ I \ e, w x := by
      simp only [FE, w, sum_filter, mul_sum, mul_ite, mul_zero]
    _ ≤ (u ^ 2 * |infiniteCenteredCoefficient L e|) *
        ∑ A ∈ IndependentExtensionDeficit.families (G \ e) (FixedPairExtensions.sourceSpace e L) L, ∏ x ∈ A, w x :=
      mul_le_mul_of_nonneg_left hfiber (mul_nonneg (pow_nonneg hu _) (abs_nonneg _))
    _ = _ := by
      rw [IndependentExtensionDeficit.deficit_eq_product_weights]
      ring

theorem pointwise (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (I : Finset ℕ) (hIG : I ⊆ G) (hnot : ¬Retained G L I) :
    (∏ x ∈ I, u * infiniteMarginal x L) ≤
      (∑ D ∈ primitives G L, if D ⊆ I then weight L u D * ∏ x ∈ I \ D, u * infiniteMarginal x L else 0) +
      ∑ e ∈ G.powersetCard 2, if e ⊆ I then u ^ 2 * |infiniteCenteredCoefficient L e| *
        ∏ x ∈ I \ e, u * infiniteMarginal x L else 0 := by
  classical
  have hpos : 0 < runRelativeNullity L I := Nat.pos_of_ne_zero fun hz ↦ hnot (Or.inl hz)
  obtain ⟨D, hDI, hprim⟩ := PrimitiveActiveSeeds.exists_primitive_subset L I hpos
  have hcard := PrimitiveActiveSeeds.primitive_card_ge_two L D hprim
  have hw (x : ℕ) : 0 ≤ u * infiniteMarginal x L := mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hnonneg (A : Finset ℕ) : 0 ≤ weight L u A * ∏ x ∈ I \ A, u * infiniteMarginal x L :=
    mul_nonneg (mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) (prod_nonneg fun x _ ↦ hw x)
  have hbound : (∏ x ∈ I, u * infiniteMarginal x L) ≤ weight L u D * ∏ x ∈ I \ D, u * infiniteMarginal x L := by
    have hsplit := prod_sdiff hDI (f := fun x ↦ u * infiniteMarginal x L)
    have hseed : (∏ x ∈ D, u * infiniteMarginal x L) ≤ weight L u D := by
      rw [prod_mul_distrib, prod_const]
      exact mul_le_mul_of_nonneg_left (UnrestrictedRetainedExpansion.primitive_independent_le L hL D hprim) (pow_nonneg hu _)
    calc
      _ = (∏ x ∈ D, u * infiniteMarginal x L) * ∏ x ∈ I \ D, u * infiniteMarginal x L := by
        rw [mul_comm, hsplit]
      _ ≤ _ := mul_le_mul_of_nonneg_right hseed (prod_nonneg fun x _ ↦ hw x)
  have hfirst : 0 ≤ ∑ A ∈ primitives G L, if A ⊆ I then weight L u A * ∏ x ∈ I \ A, u * infiniteMarginal x L else 0 := by
    exact sum_nonneg fun A _ ↦ by split_ifs; exacts [hnonneg A, le_rfl]
  have hsecond : 0 ≤ ∑ e ∈ G.powersetCard 2, if e ⊆ I then u ^ 2 * |infiniteCenteredCoefficient L e| *
      ∏ x ∈ I \ e, u * infiniteMarginal x L else 0 := by
    exact sum_nonneg fun e _ ↦ by split_ifs; exacts [mul_nonneg (mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) (prod_nonneg fun x _ ↦ hw x), le_rfl]
  by_cases htwo : D.card = 2
  · have hD : D ∈ G.powersetCard 2 := mem_powersetCard.mpr ⟨hDI.trans hIG, htwo⟩
    have hsingle := single_le_sum (s := G.powersetCard 2)
      (f := fun e ↦ if e ⊆ I then u ^ 2 * |infiniteCenteredCoefficient L e| * ∏ x ∈ I \ e, u * infiniteMarginal x L else 0)
      (fun e _ ↦ by split_ifs; exacts [mul_nonneg (mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) (prod_nonneg fun x _ ↦ hw x), le_rfl]) hD
    rw [ite_eq_left hDI] at hsingle
    dsimp only [weight] at hbound
    rw [htwo] at hbound
    linarith only [hbound, hsingle, hfirst]
  · have hD : D ∈ primitives G L := mem_filter.mpr ⟨mem_powerset.mpr (hDI.trans hIG), by omega, hprim⟩
    have hsingle := single_le_sum (s := primitives G L)
      (f := fun A ↦ if A ⊆ I then weight L u A * ∏ x ∈ I \ A, u * infiniteMarginal x L else 0)
      (fun A _ ↦ by split_ifs; exacts [hnonneg A, le_rfl]) hD
    rw [ite_eq_left hDI] at hsingle
    linarith only [hbound, hsingle, hsecond]

theorem independent_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L) (u : ℝ) (hu : 0 ≤ u)
    (F : Finset (Finset ℕ)) (hF : ∀ I ∈ F, I ⊆ G ∧ ¬Retained G L I) :
    (∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L) ≤
      Real.exp (∑ x ∈ G, u * infiniteMarginal x L) * ∑ D ∈ primitives G L, weight L u D +
        u ^ 2 * AllPairExtensionDeficit.deficit G L u := by
  have hseed := SeedComplementSum.finite_bound G F (primitives G L) (fun x ↦ u * infiniteMarginal x L)
    (weight L u) (fun x ↦ mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L))
    (fun D _ ↦ mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) (fun I hI ↦ (hF I hI).1)
    (fun D hD ↦ mem_powerset.mp (mem_filter.mp hD).1)
  have hp := pair_bound G L u hu F hF
  have hpoint := sum_le_sum fun I hI ↦ pointwise G L hL u hu I (hF I hI).1 (hF I hI).2
  simp only [sum_add_distrib] at hpoint
  linarith only [hseed, hp, hpoint]

end PaperP1.SecondOrderIndependentDeficit
