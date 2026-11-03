module

public import PaperP1.Algebra.FiniteRootWordSquares
public import PaperP1.Algebra.IndependentQuadraticTower

/-! # Independent disjoint finite field-root lists give the actual generic radical field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteRootWordField

open Finset Polynomial PaperP1.FiniteRootWordSquares PaperP1.FiniteQuadraticTower

theorem linear_biUnion {F ι : Type*} [Field F] [DecidableEq F]
    (A : Finset ι) (I : ι → Finset F) (hI : (A : Set ι).PairwiseDisjoint I) :
    linear (A.biUnion I) = ∏ i ∈ A, linear (I i) := prod_biUnion hI

theorem word_biUnion {F ι : Type*} [Field F] [DecidableEq F]
    (A : Finset ι) (I J : ι → Finset F)
    (hI : (A : Set ι).PairwiseDisjoint I) (hJ : (A : Set ι).PairwiseDisjoint J) :
    word (A.biUnion I) (A.biUnion J) = ∏ i ∈ A, word (I i) (J i) := by
  rw [word, linear_biUnion A I hI, linear_biUnion A J hJ]
  simp only [map_prod, Polynomial.map_prod, word, prod_mul_distrib]

theorem polynomial_product {F ι : Type*} [Field F] [DecidableEq F]
    (A : Finset ι) (c : ι → F) (I J : ι → Finset F)
    (hI : (A : Set ι).PairwiseDisjoint I) (hJ : (A : Set ι).PairwiseDisjoint J) :
    (∏ i ∈ A, scaledPolynomial (c i) (I i) (J i)) =
      scaledPolynomial (∏ i ∈ A, c i) (A.biUnion I) (A.biUnion J) := by
  rw [scaledPolynomial, word_biUnion A I J hI hJ]
  simp only [scaledPolynomial, map_prod, prod_mul_distrib]

theorem function_product {F ι : Type*} [Field F] [DecidableEq F]
    (A : Finset ι) (c : ι → F) (I J : ι → Finset F)
    (hI : (A : Set ι).PairwiseDisjoint I) (hJ : (A : Set ι).PairwiseDisjoint J) :
    (∏ i ∈ A, scaledFunction (c i) (I i) (J i)) =
      scaledFunction (∏ i ∈ A, c i) (A.biUnion I) (A.biUnion J) := by
  simp only [scaledFunction, ← map_prod, polynomial_product A c I J hI hJ]

theorem product_not_square {F ι : Type*} [Field F] [DecidableEq F]
    (A : Finset ι) (hA : A.Nonempty) (c : ι → F) (I J : ι → Finset F)
    (hc : ∀ i ∈ A, c i ≠ 0) (hne : ∀ i ∈ A, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : (A : Set ι).PairwiseDisjoint I) (hJ : (A : Set ι).PairwiseDisjoint J) :
    ¬ IsSquare (∏ i ∈ A, scaledFunction (c i) (I i) (J i)) := by
  rw [function_product A c I J hI hJ]
  apply function_not_square _ (prod_ne_zero_iff.mpr hc)
  obtain ⟨i, hi⟩ := hA
  rcases hne i hi with hleft | hright
  · obtain ⟨a, ha⟩ := hleft
    exact Or.inl ⟨a, mem_biUnion.mpr ⟨i, hi, ha⟩⟩
  · obtain ⟨a, ha⟩ := hright
    exact Or.inr ⟨a, mem_biUnion.mpr ⟨i, hi, ha⟩⟩

theorem list_independent {F ι : Type*} [Field F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset F)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IndependentQuadraticTower.Independent (l.map fun i ↦ scaledFunction (c i) (I i) (J i)) := by
  classical
  intro t ht htne
  obtain ⟨r, hr, rfl⟩ := List.sublist_map_iff.mp ht
  have hrnodup := hl.sublist hr
  have hrnonempty : r.toFinset.Nonempty := by
    by_contra hh
    have hrnil : r = [] := by
      have hh' : r.toFinset = ∅ := not_nonempty_iff_eq_empty.mp hh
      simpa only [List.toFinset_eq_empty_iff] using hh'
    exact htne (by simp only [hrnil, List.map_nil])
  have hnot := product_not_square r.toFinset hrnonempty c I J (fun i _ ↦ hc i) (fun i _ ↦ hne i)
    (fun i _ j _ hij ↦ hI hij) (fun i _ j _ hij ↦ hJ hij)
  rwa [List.prod_toFinset (fun i ↦ scaledFunction (c i) (I i) (J i)) hrnodup] at hnot

theorem source_field {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset F)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsField (Tower (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i))) ∧
      Module.finrank (FunctionField F) (Tower (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i))) = 2 ^ l.length := by
  refine ⟨IndependentQuadraticTower.isField _ _ (list_independent l hl c hc I J hne hI hJ), ?_⟩
  simpa only [List.length_map] using finrank (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i))

end PaperP1.FiniteRootWordField
