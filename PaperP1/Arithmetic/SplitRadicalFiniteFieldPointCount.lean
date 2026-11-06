module

public import PaperP1.Arithmetic.SeparatedQuadraticPointError
public import PaperP1.Algebra.SplitRadicalCoordinateAlgebra

/-! # The exact character expansion belongs to the actual split-radical equations of the paper -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalFiniteFieldPointCount

open Finset Polynomial
open scoped Classical

def linearValue (F : Type*) [Field F] (I : Finset ℤ) (x : F) : F :=
  ∏ a ∈ I, (x + (a : F))

def points {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (c : ι → F) (I J : ι → Finset ℤ) : Finset ((F × F) × (ι → F)) :=
  SeparatedQuadraticPointCount.points c (fun i ↦ linearValue F (I i)) (fun i ↦ linearValue F (J i))

theorem mem_points_iff {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (c : ι → F) (I J : ι → Finset ℤ) (w : (F × F) × (ι → F)) :
    w ∈ points c I J ↔ ∀ i, w.2 i ^ 2 =
      (ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i)).evalEval w.1.1 w.1.2 := by
  rw [points, SeparatedQuadraticPointCount.mem_points]
  simp only [SplitRadicalCoordinateAlgebra.equation_evaluation, linearValue]

theorem product_linearValue {F ι : Type*} [Field F] (I : ι → Finset ℤ) (s : Finset ι)
    (hI : Set.PairwiseDisjoint (s : Set ι) I) (x : F) :
    (∏ i ∈ s, linearValue F (I i) x) = linearValue F (s.biUnion I) x := by
  exact (Finset.prod_biUnion hI).symm

theorem character_sum_union {F ι : Type*} [Field F] [Fintype F]
    (I : ι → Finset ℤ) (s : Finset ι) (hI : Set.PairwiseDisjoint (s : Set ι) I) :
    SeparatedQuadraticPointCount.characterSum (fun i ↦ linearValue F (I i)) s =
      ∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x) := by
  unfold SeparatedQuadraticPointCount.characterSum
  exact sum_congr rfl (fun x _ ↦ congrArg (quadraticChar F) (product_linearValue I s hI x))

theorem character_expansion {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (hodd : ringChar F ≠ 2) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    ((points c I J).card : ℤ) = ∑ s ∈ (univ : Finset ι).powerset,
      quadraticChar F (∏ i ∈ s, c i) *
        (∑ x : F, quadraticChar F (linearValue F (s.biUnion I) x)) *
        (∑ y : F, quadraticChar F (linearValue F (s.biUnion J) y)) := by
  rw [points, SeparatedQuadraticPointCount.character_expansion hodd]
  apply sum_congr rfl
  intro s _
  rw [character_sum_union I s (fun i _ j _ hij ↦ hI hij),
    character_sum_union J s (fun i _ j _ hij ↦ hJ hij)]

end PaperP1.SplitRadicalFiniteFieldPointCount
