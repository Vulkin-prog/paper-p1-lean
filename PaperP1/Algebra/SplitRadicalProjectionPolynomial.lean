module

public import PaperP1.Algebra.RadicalProjectionPowerBasis
public import PaperP1.Algebra.SplitRadicalCoordinateAlgebra
public import PaperP1.Algebra.TrivariatePolynomialEvaluation

/-! # The actual split-radical image equation, its degrees, and all source points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalProjectionPolynomial

open Finset Polynomial Module PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.ScaledSplitWordSquares PaperP1.SplitRadicalCoordinateAlgebra
  PaperP1.RadicalProjectionPolynomial PaperP1.TrivariatePolynomialEquiv

def sourceEquation {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) : F[X][X][X] :=
  equation F[X][X] (radicands l c I J)

def sourceSurfaceEquation {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) : MvPolynomial (Fin 3) F :=
  asMvPolynomial F (sourceEquation l c I J)

theorem generic_independent {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IndependentQuadraticTower.Independent ((radicands l c I J).map (algebraMap F[X][X] (FunctionField F))) := by
  rw [generic_radicands]
  exact SplitRadicalField.list_independent l hl c hc I J hne hI hJ

theorem source_monic {F ι : Type*} [Field F] (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) :
    (sourceEquation l c I J).Monic := equation_monic _ _

theorem source_equation_degree {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    (sourceEquation l c I J).natDegree = 2 ^ l.length := by
  simpa only [sourceEquation, radicands, List.length_map] using
    equation_degree F[X][X] (FunctionField F) (radicands l c I J) (generic_independent l hl c hc I J hne hI hJ)

theorem source_equation_irreducible {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    Irreducible (sourceEquation l c I J) :=
  equation_irreducible F[X][X] (FunctionField F) (radicands l c I J) (generic_independent l hl c hc I J hne hI hJ)

theorem source_surface_irreducible {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    Irreducible (sourceSurfaceEquation l c I J) :=
  (TrivariatePolynomialEquiv.irreducible_iff F _).mpr (source_equation_irreducible l hl c hc I J hne hI hJ)

theorem source_surface_degree_lower {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    2 ^ l.length ≤ (sourceSurfaceEquation l c I J).totalDegree := by
  rw [← source_equation_degree l hl c hc I J hne hI hJ]
  exact natDegree_le_totalDegree F _

theorem source_image_free_rank {F ι : Type*} [Field F] [CharZero F]
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    Module.Free F[X][X] (imageAlgebra F[X][X] (radicands l c I J)) ∧
      Module.Finite F[X][X] (imageAlgebra F[X][X] (radicands l c I J)) ∧
      finrank F[X][X] (imageAlgebra F[X][X] (radicands l c I J)) = 2 ^ l.length := by
  have hs := generic_independent l hl c hc I J hne hI hJ
  refine ⟨RadicalProjectionPowerBasis.image_free _ (FunctionField F) _ hs,
    RadicalProjectionPowerBasis.image_finite _ (FunctionField F) _ hs, ?_⟩
  simpa only [radicands, List.length_map] using RadicalProjectionPowerBasis.image_finrank F[X][X] (FunctionField F) _ hs

theorem source_points_vanish {F ι : Type*} [Field F]
    (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) (x y : F)
    (w : Fin (radicands l c I J).length → F)
    (hw : ∀ i, w i ^ 2 = ((radicands l c I J).get i).evalEval x y) :
    ((sourceEquation l c I J).map (evalEvalRingHom x y)).eval (∑ i, w i) = 0 := by
  obtain ⟨ψ, ⟨hbase, hroots⟩, _hunique⟩ := actual_point_map l c I J x y w hw
  have hsum : ψ (radicalSum F[X][X] (radicands l c I J)) = ∑ i, w i := by
    rw [radicalSum, map_sum]
    exact sum_congr rfl (fun i _ ↦ hroots i)
  have hcomm : (algebraMap F F).comp (evalEvalRingHom x y) =
      ψ.comp (algebraMap F[X][X] (CoordinateAlgebra l c I J)) := by
    apply RingHom.ext
    intro P
    exact (hbase P).symm
  have hh := map_aeval_eq_aeval_map hcomm (equation F[X][X] (radicands l c I J))
    (radicalSum F[X][X] (radicands l c I J))
  rw [equation_root, map_zero, hsum] at hh
  simpa only [sourceEquation, aeval_def, Algebra.algebraMap_self, eval₂_id] using hh.symm

theorem source_surface_points_vanish {F ι : Type*} [Field F]
    (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) (x y : F)
    (w : Fin (radicands l c I J).length → F)
    (hw : ∀ i, w i ^ 2 = ((radicands l c I J).get i).evalEval x y) :
    MvPolynomial.eval ![∑ i, w i, y, x] (sourceSurfaceEquation l c I J) = 0 := by
  rw [sourceSurfaceEquation, TrivariatePolynomialEvaluation.asMvPolynomial_eval]
  exact source_points_vanish l c I J x y w hw

end PaperP1.SplitRadicalProjectionPolynomial
