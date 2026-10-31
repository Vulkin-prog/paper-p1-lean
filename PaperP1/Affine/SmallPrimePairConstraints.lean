module

public import PaperP1.Affine.TwoWindowRelations
public import PaperP1.Combinatorics.LargePrimeGraphResolution
public import PaperP1.Coding.LocalDefectBound

/-! # The finite rank cost of completing the large-prime equations

After the large primes are imposed, all remaining constraints are the actual
π(10B) small-prime coordinates and the separate parities of the two blocks.
Their kernel is explicitly equivalent to the complete even-relation code.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Affine

open PaperP1.Arithmetic LargePrimeOccurrences LargePrimeGraph LargePrimeGraphResolution
open LocalDefectBound Finset

local instance smallPairConstraintPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

abbrev SmallPairConstraintTarget (L : ℕ) :=
  (Fin (primeCount (10 * (L + 1))) → F₂) × F₂ × F₂

def pairSmallConstraintMap (x y L : ℕ) : (Occurrence L → F₂) →ₗ[F₂]
    SmallPairConstraintTarget L where
  toFun w := (fun i ↦ pairVertexParityMap x y L w (smallPrime (10 * (L + 1)) i),
    pairLeftSum L w, pairRightSum L w)
  map_add' u v := by
    apply Prod.ext
    · funext i
      simp
    · apply Prod.ext <;> simp
  map_smul' a u := by
    apply Prod.ext
    · funext i
      simp [Finsupp.smul_apply]
    · apply Prod.ext <;> simp

def largeSpaceSmallConstraints (x y L : ℕ) : largePrimeSolution x y L →ₗ[F₂]
    SmallPairConstraintTarget L :=
  (pairSmallConstraintMap x y L).comp (largePrimeSolution x y L).subtype

theorem pairVertexParityMap_coord (x y L : ℕ) (w : Occurrence L → F₂) (p : ℕ) :
    pairVertexParityMap x y L w p = ∑ v, w v *
      parityVec (twoStartCompleteVertexLabel x y L v) p := by
  rw [pairVertexParityMap, Fintype.linearCombination_apply]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem completeRelation_mem_largePrime {x y L : ℕ} (w : completeRelationCode x y L) :
    w.val ∈ largePrimeSolution x y L := by
  have hw := (mem_completeRelationCode w.val).mp w.property
  apply mem_largePrimeSolution_iff_boundary_prime_equations.mpr
  intro p _hp
  rw [← pairVertexParityMap_coord, hw.1, Finsupp.zero_apply]

theorem parity_zero_of_large_and_small {x y L : ℕ} (w : largePrimeSolution x y L)
    (hsmall : ∀ i : Fin (primeCount (10 * (L + 1))),
      pairVertexParityMap x y L w.val (smallPrime (10 * (L + 1)) i) = 0) :
    pairVertexParityMap x y L w.val = 0 := by
  apply Finsupp.ext
  intro p
  by_cases hp : p.Prime
  · by_cases hlarge : 10 * (L + 1) < p
    · rw [pairVertexParityMap_coord]
      exact (mem_largePrimeSolution_iff_boundary_prime_equations.mp w.property) p ⟨hp, hlarge⟩
    · obtain ⟨i, hi⟩ := smallPrime_covers hp (Nat.le_of_not_gt hlarge)
      simpa only [hi, Finsupp.zero_apply] using hsmall i
  · rw [pairVertexParityMap_coord]
    apply sum_eq_zero
    intro v _
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_prime _ hp, Nat.cast_zero,
      mul_zero]

theorem mem_ker_largeSpaceSmallConstraints {x y L : ℕ} (w : largePrimeSolution x y L) :
    w ∈ LinearMap.ker (largeSpaceSmallConstraints x y L) ↔
      (∀ i : Fin (primeCount (10 * (L + 1))),
        pairVertexParityMap x y L w.val (smallPrime (10 * (L + 1)) i) = 0) ∧
      (∑ i, w.val (Sum.inl i)) = 0 ∧ (∑ i, w.val (Sum.inr i)) = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact congrArg (fun t : SmallPairConstraintTarget L ↦ t.1 i) h
    · exact congrArg (fun t : SmallPairConstraintTarget L ↦ t.2.1) h
    · exact congrArg (fun t : SmallPairConstraintTarget L ↦ t.2.2) h
  · rintro ⟨hs, hl, hr⟩
    apply Prod.ext
    · exact funext hs
    · exact Prod.ext hl hr

def completeRelationEquivConstraintKer (x y L : ℕ) : completeRelationCode x y L ≃ₗ[F₂]
    LinearMap.ker (largeSpaceSmallConstraints x y L) where
  toFun w := by
    have hw := (mem_completeRelationCode w.val).mp w.property
    refine ⟨⟨w.val, completeRelation_mem_largePrime w⟩, ?_⟩
    apply (mem_ker_largeSpaceSmallConstraints _).mpr
    refine ⟨?_, hw.2.1, hw.2.2⟩
    intro i
    rw [hw.1, Finsupp.zero_apply]
  invFun w := by
    have hw := (mem_ker_largeSpaceSmallConstraints w.val).mp w.property
    exact ⟨w.val.val, (mem_completeRelationCode _).mpr
      ⟨parity_zero_of_large_and_small w.val hw.1, hw.2.1, hw.2.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem finrank_smallPairConstraintTarget (L : ℕ) :
    Module.finrank F₂ (SmallPairConstraintTarget L) = primeCount (10 * (L + 1)) + 2 := by
  simp only [SmallPairConstraintTarget, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Module.finrank_self]

theorem complete_relation_rank_le_large (x y L : ℕ) :
    Module.finrank F₂ (completeRelationCode x y L) ≤
      Module.finrank F₂ (largePrimeSolution x y L) := by
  rw [(completeRelationEquivConstraintKer x y L).finrank_eq]
  exact Submodule.finrank_le _

theorem large_relation_rank_le_complete_add_cost (x y L : ℕ) :
    Module.finrank F₂ (largePrimeSolution x y L) ≤
      Module.finrank F₂ (completeRelationCode x y L) + primeCount (10 * (L + 1)) + 2 := by
  have hdim := (largeSpaceSmallConstraints x y L).finrank_range_add_finrank_ker
  have hrange := Submodule.finrank_le (LinearMap.range (largeSpaceSmallConstraints x y L))
  rw [finrank_smallPairConstraintTarget] at hrange
  have hker := (completeRelationEquivConstraintKer x y L).finrank_eq
  omega

end PaperP1.Affine
