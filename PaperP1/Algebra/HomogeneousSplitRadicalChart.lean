module

public import PaperP1.Algebra.HomogeneousSplitRadicalAlgebra
public import PaperP1.Algebra.SplitRadicalCoordinateAlgebra

/-! # The literal chart Z=1 specializes the homogeneous equations to the actual affine system -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalChart

open Finset Polynomial PaperP1.HomogeneousSplitRadicalData

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing F[X][X] := inferInstance

def chart (F : Type*) [Field F] : PolynomialRing F →+* F[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (evalRingHom (1 : F)))

theorem linear_chart (F : Type*) [Field F] (I : Finset ℤ) :
    (linear F I).map (evalRingHom (1 : F)) = FormalWordPolynomials.linearOver F I := by
  have hcoef : ∀ i : ℤ, (evalRingHom (1 : F)) ((i : F[X]) * (X : F[X])) = (i : F) := by
    intro i
    simp
  simp only [linear, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    hcoef, FormalWordPolynomials.linearOver]

theorem word_chart (F : Type*) [Field F] (I J : Finset ℤ) :
    chart F (word F I J) = FormalWordPolynomials.wordOver F I J := by
  change (word F I J).map (Polynomial.mapRingHom (evalRingHom (1 : F))) = _
  rw [word, Polynomial.map_mul, Polynomial.map_C]
  change C ((linear F I).map (evalRingHom (1 : F))) *
    ((linear F J).map C).map (Polynomial.mapRingHom (evalRingHom (1 : F))) = _
  rw [linear_chart, Polynomial.map_map]
  have he : (Polynomial.mapRingHom (evalRingHom (1 : F))).comp (C (R := F[X])) =
      (C (R := F)).comp (evalRingHom (1 : F)) := by
    apply RingHom.ext
    intro p
    change (C p).map (evalRingHom (1 : F)) = C ((evalRingHom (1 : F)) p)
    rw [Polynomial.map_C]
  rw [he, ← Polynomial.map_map, linear_chart]
  rfl

theorem radicand_chart {F : Type*} [Field F] (c : F) (e : ℕ) (I J : Finset ℤ) :
    chart F (radicand c e I J) = ScaledSplitWordSquares.scaledPolynomial c I J := by
  change (C (C (C c * (X : F[X]) ^ e)) * word F I J).map (Polynomial.mapRingHom (evalRingHom (1 : F))) = _
  rw [Polynomial.map_mul, Polynomial.map_C]
  change C ((C (C c * (X : F[X]) ^ e)).map (evalRingHom (1 : F))) * chart F (word F I J) = _
  rw [Polynomial.map_C, word_chart]
  simp only [coe_evalRingHom, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one,
    ScaledSplitWordSquares.scaledPolynomial]

theorem radicands_chart {F ι : Type*} [Field F]
    (l : List ι) (c : ι → F) (e : ι → ℕ) (I J : ι → Finset ℤ) :
    (HomogeneousSplitRadicalAlgebra.radicands l c e I J).map (chart F) =
      SplitRadicalCoordinateAlgebra.radicands l c I J := by
  simp only [HomogeneousSplitRadicalAlgebra.radicands, SplitRadicalCoordinateAlgebra.radicands,
    List.map_map, Function.comp_def, radicand_chart]

theorem chart_map_exists {F ι : Type*} [Field F]
    (l : List ι) (c : ι → F) (e : ι → ℕ) (I J : ι → Finset ℤ) :
    ∃ φ : HomogeneousSplitRadicalAlgebra.CoordinateAlgebra l c e I J →+*
        SplitRadicalCoordinateAlgebra.CoordinateAlgebra l c I J,
      ∀ P : PolynomialRing F,
        φ (algebraMap (PolynomialRing F) (HomogeneousSplitRadicalAlgebra.CoordinateAlgebra l c e I J) P) =
          algebraMap F[X][X] (SplitRadicalCoordinateAlgebra.CoordinateAlgebra l c I J) (chart F P) := by
  let s := HomogeneousSplitRadicalAlgebra.radicands l c e I J
  let d := QuadraticTowerBaseChange.mapData (chart F) s
  have hh : ∃ φ : FiniteQuadraticTower.Tower (PolynomialRing F) s →+*
      FiniteQuadraticTower.Tower F[X][X] (s.map (chart F)),
      ∀ P : PolynomialRing F, φ (algebraMap (PolynomialRing F) (FiniteQuadraticTower.Tower (PolynomialRing F) s) P) =
        algebraMap F[X][X] (FiniteQuadraticTower.Tower F[X][X] (s.map (chart F))) (chart F P) :=
    ⟨d.hom, d.commutes⟩
  let Q (t : List F[X][X]) : Prop :=
    ∃ φ : FiniteQuadraticTower.Tower (PolynomialRing F) s →+* FiniteQuadraticTower.Tower F[X][X] t,
      ∀ P : PolynomialRing F,
        φ (algebraMap (PolynomialRing F) (FiniteQuadraticTower.Tower (PolynomialRing F) s) P) =
          algebraMap F[X][X] (FiniteQuadraticTower.Tower F[X][X] t) (chart F P)
  change Q (SplitRadicalCoordinateAlgebra.radicands l c I J)
  exact (radicands_chart l c e I J) ▸ (hh : Q (s.map (chart F)))

end PaperP1.HomogeneousSplitRadicalChart
