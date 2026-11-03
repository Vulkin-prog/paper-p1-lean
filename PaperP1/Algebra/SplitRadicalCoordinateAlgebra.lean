module

public import PaperP1.Algebra.SplitRadicalField
public import PaperP1.Algebra.QuadraticTowerBaseChange
public import PaperP1.Algebra.QuadraticTowerPoints

/-! # The literal split-radical coordinate algebra is a domain and represents the actual point equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalCoordinateAlgebra

open Finset Polynomial PaperP1.ScaledSplitWordSquares PaperP1.FiniteQuadraticTower
  PaperP1.FormalWordPolynomials

def radicands {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) : List F[X][X] :=
  l.map fun i ↦ scaledPolynomial (c i) (I i) (J i)

abbrev CoordinateAlgebra {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) :=
  Tower F[X][X] (radicands l c I J)

theorem generic_radicands {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) :
    (radicands l c I J).map (algebraMap F[X][X] (FunctionField F)) =
      l.map (fun i ↦ scaledFunction (c i) (I i) (J i)) := by
  rw [radicands, List.map_map]
  rfl

theorem coordinate_isDomain {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsDomain (CoordinateAlgebra l c I J) := by
  apply QuadraticTowerBaseChange.source_isDomain (algebraMap F[X][X] (FunctionField F))
    (IsFractionRing.injective F[X][X] (FunctionField F)) (radicands l c I J)
  rw [generic_radicands]
  exact (SplitRadicalField.source_field l hl c hc I J hne hI hJ).1.isDomain

theorem equation_evaluation {F : Type*} [Field F] (c x y : F) (I J : Finset ℤ) :
    (scaledPolynomial c I J).evalEval x y = c *
      (∏ i ∈ I, (x + (i : F))) * ∏ j ∈ J, (y + (j : F)) := by
  simp only [scaledPolynomial, wordOver, evalEval_mul, evalEval_C, eval_C, evalEval_map_C,
    linearOver, eval_prod, eval_add, eval_X]
  ring

theorem actual_point_map {F ι : Type*} [Field F]
    (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) (x y : F)
    (w : Fin (radicands l c I J).length → F)
    (hw : ∀ i, w i ^ 2 = ((radicands l c I J).get i).evalEval x y) :
    ∃! ψ : CoordinateAlgebra l c I J →+* F,
      (∀ P : F[X][X], ψ (algebraMap F[X][X] (CoordinateAlgebra l c I J) P) = P.evalEval x y) ∧
      ∀ i, ψ (root F[X][X] (radicands l c I J) i) = w i := by
  exact QuadraticTowerPoints.unique_ringHom F[X][X] F (evalEvalRingHom x y) (radicands l c I J) w hw

end PaperP1.SplitRadicalCoordinateAlgebra
