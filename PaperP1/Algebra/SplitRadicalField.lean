module

public import PaperP1.Algebra.IndependentQuadraticTower
public import PaperP1.Algebra.DisjointSplitSquareClasses

/-! # The actual generic split-radical tower is a field of degree two to the number of equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalField

open Finset PaperP1.ScaledSplitWordSquares PaperP1.FiniteQuadraticTower

theorem list_independent {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
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
  have hnot := DisjointSplitSquareClasses.product_not_square r.toFinset hrnonempty c I J
    (fun i _ ↦ hc i) (fun i _ ↦ hne i) (fun i _ j _ hij ↦ hI hij) (fun i _ j _ hij ↦ hJ hij)
  rwa [List.prod_toFinset (fun i ↦ scaledFunction (c i) (I i) (J i)) hrnodup] at hnot

theorem source_field {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsField (Tower (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i))) ∧
      Module.finrank (FunctionField F) (Tower (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i))) = 2 ^ l.length := by
  refine ⟨IndependentQuadraticTower.isField _ _ (list_independent l hl c hc I J hne hI hJ), ?_⟩
  simpa only [List.length_map] using finrank (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i))

end PaperP1.SplitRadicalField
