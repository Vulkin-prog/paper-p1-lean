module

public import PaperP1.Algebra.ScaledSplitWordSquares
public import PaperP1.Algebra.FieldSquareClasses
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # The actual square classes of disjoint multiquadratic split radicands are linearly independent -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointSplitSquareClasses

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.ScaledSplitWordSquares

theorem linear_biUnion {F ι : Type*} [Field F] (A : Finset ι) (I : ι → Finset ℤ)
    (hI : (↑A : Set ι).PairwiseDisjoint I) :
    linearOver F (A.biUnion I) = ∏ i ∈ A, linearOver F (I i) := prod_biUnion hI

theorem word_biUnion {F ι : Type*} [Field F] (A : Finset ι) (I J : ι → Finset ℤ)
    (hI : (↑A : Set ι).PairwiseDisjoint I) (hJ : (↑A : Set ι).PairwiseDisjoint J) :
    wordOver F (A.biUnion I) (A.biUnion J) = ∏ i ∈ A, wordOver F (I i) (J i) := by
  rw [wordOver, linear_biUnion A I hI, linear_biUnion A J hJ]
  simp only [map_prod, Polynomial.map_prod, wordOver, prod_mul_distrib]

theorem polynomial_product {F ι : Type*} [Field F] (A : Finset ι) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : (↑A : Set ι).PairwiseDisjoint I) (hJ : (↑A : Set ι).PairwiseDisjoint J) :
    (∏ i ∈ A, scaledPolynomial (c i) (I i) (J i)) =
      scaledPolynomial (∏ i ∈ A, c i) (A.biUnion I) (A.biUnion J) := by
  rw [scaledPolynomial, word_biUnion A I J hI hJ]
  simp only [scaledPolynomial, map_prod, prod_mul_distrib]

theorem function_product {F ι : Type*} [Field F] (A : Finset ι) (c : ι → F) (I J : ι → Finset ℤ)
    (hI : (↑A : Set ι).PairwiseDisjoint I) (hJ : (↑A : Set ι).PairwiseDisjoint J) :
    (∏ i ∈ A, scaledFunction (c i) (I i) (J i)) =
      scaledFunction (∏ i ∈ A, c i) (A.biUnion I) (A.biUnion J) := by
  simp only [scaledFunction, ← map_prod, polynomial_product A c I J hI hJ]

theorem product_not_square {F ι : Type*} [Field F] [CharZero F]
    (A : Finset ι) (hA : A.Nonempty) (c : ι → F) (I J : ι → Finset ℤ)
    (hc : ∀ i ∈ A, c i ≠ 0) (hne : ∀ i ∈ A, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : (↑A : Set ι).PairwiseDisjoint I) (hJ : (↑A : Set ι).PairwiseDisjoint J) :
    ¬ IsSquare (∏ i ∈ A, scaledFunction (c i) (I i) (J i)) := by
  rw [function_product A c I J hI hJ]
  apply function_not_square _ (prod_ne_zero_iff.mpr hc)
  obtain ⟨i, hi⟩ := hA
  rcases hne i hi with hleft | hright
  · obtain ⟨a, ha⟩ := hleft
    exact Or.inl ⟨a, mem_biUnion.mpr ⟨i, hi, ha⟩⟩
  · obtain ⟨a, ha⟩ := hright
    exact Or.inr ⟨a, mem_biUnion.mpr ⟨i, hi, ha⟩⟩

def squareClass {F : Type*} [Field F] [CharZero F] (c : F) (hc : c ≠ 0) (I J : Finset ℤ) :
    FieldSquareClasses.Classes (FunctionField F) :=
  FieldSquareClasses.ofNonzero (scaledFunction c I J) (function_ne_zero c hc I J)

theorem nonempty_sum_ne_zero {F ι : Type*} [Field F] [CharZero F]
    (A : Finset ι) (hA : A.Nonempty) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : (↑A : Set ι).PairwiseDisjoint I) (hJ : (↑A : Set ι).PairwiseDisjoint J) :
    (∑ i ∈ A, squareClass (c i) (hc i) (I i) (J i)) ≠ 0 := by
  simp only [squareClass]
  rw [← FieldSquareClasses.ofNonzero_prod A (fun i ↦ scaledFunction (c i) (I i) (J i))
    (fun i ↦ function_ne_zero (c i) (hc i) (I i) (J i))]
  intro hzero
  have hsquare := (FieldSquareClasses.ofNonzero_zero_iff _ _).mp hzero
  exact product_not_square A hA c I J (fun i _ ↦ hc i) (fun i _ ↦ hne i) hI hJ hsquare

theorem linearIndependent {F ι : Type*} [Field F] [CharZero F]
    (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    LinearIndependent (ZMod 2) (fun i ↦ squareClass (c i) (hc i) (I i) (J i)) := by
  classical
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [linearIndependent_iff']
  intro A g hsum i hi
  let B := A.filter fun j ↦ g j ≠ 0
  have hBsum : (∑ j ∈ B, squareClass (c j) (hc j) (I j) (J j)) = 0 := by
    have heq : (∑ j ∈ B, squareClass (c j) (hc j) (I j) (J j)) =
        ∑ j ∈ A, g j • squareClass (c j) (hc j) (I j) (J j) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      rcases hbinary (g j) with hz | ho
      · simp only [hz, ne_self_iff_false, ite_false, zero_smul]
      · simp only [ho, one_smul]
        norm_num
    exact heq.trans hsum
  by_contra hgi
  have hB : B.Nonempty := ⟨i, mem_filter.mpr ⟨hi, hgi⟩⟩
  exact nonempty_sum_ne_zero B hB c hc I J hne
    (fun a _ b _ hab ↦ hI hab) (fun a _ b _ hab ↦ hJ hab) hBsum

end PaperP1.DisjointSplitSquareClasses
