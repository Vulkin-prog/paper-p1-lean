module

public import PaperP1.Algebra.BirationalRadicalProjection
public import PaperP1.Algebra.SplitRadicalCoordinateAlgebra

/-! # The literal split-radical projection is finite and induces the same function field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalBirationalProjection

open Finset Polynomial PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.ScaledSplitWordSquares PaperP1.SplitRadicalCoordinateAlgebra

theorem source_sum_primitive {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    imageAlgebra (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i)) = ⊤ ∧
      (minpoly (FunctionField F)
        (radicalSum (FunctionField F) (l.map fun i ↦ scaledFunction (c i) (I i) (J i)))).natDegree = 2 ^ l.length := by
  obtain ⟨hgen, hdeg⟩ := PrimitiveRadicalSum.independent_sum_primitive (FunctionField F) _
    (SplitRadicalField.list_independent l hl c hc I J hne hI hJ)
  exact ⟨hgen, by simpa only [List.length_map] using hdeg⟩

theorem source_fractionFields {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    ∃ e : FractionRing (imageAlgebra F[X][X] (radicands l c I J)) ≃+*
        FractionRing (CoordinateAlgebra l c I J),
      ∀ b : imageAlgebra F[X][X] (radicands l c I J),
        e (algebraMap (imageAlgebra F[X][X] (radicands l c I J))
          (FractionRing (imageAlgebra F[X][X] (radicands l c I J))) b) =
            algebraMap (CoordinateAlgebra l c I J) (FractionRing (CoordinateAlgebra l c I J))
              (b : CoordinateAlgebra l c I J) := by
  apply BirationalRadicalProjection.fractionField_equiv F[X][X] (FunctionField F)
  rw [generic_radicands]
  exact SplitRadicalField.list_independent l hl c hc I J hne hI hJ

end PaperP1.SplitRadicalBirationalProjection
