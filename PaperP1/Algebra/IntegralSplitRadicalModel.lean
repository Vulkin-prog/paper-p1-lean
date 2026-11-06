module

public import PaperP1.Algebra.SplitRadicalCoordinateAlgebra
public import PaperP1.Algebra.QuadraticTowerListCongr
public import PaperP1.Algebra.QuadraticTowerGeneratorBaseChange

/-! # One literal integer split-radical source specializes to every actual field source -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegralSplitRadicalModel
open Polynomial Finset FiniteQuadraticTower
open scoped Classical

def linear (I : Finset ℤ) : ℤ[X] := ∏ a ∈ I, (X + C a)
def radicand (c : ℤ) (I J : Finset ℤ) : ℤ[X][X] := C (C c) * (C (linear I) * (linear J).map C)
def equations {ι : Type*} (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) : List ℤ[X][X] :=
  l.map (fun i ↦ radicand (c i) (I i) (J i))
abbrev Source {ι : Type*} (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) := Tower ℤ[X][X] (equations l c I J)

def coefficientMap (F : Type*) [Field F] : ℤ[X][X] →+* F[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom F))

theorem linear_map (F : Type*) [Field F] (I : Finset ℤ) :
    (linear I).map (Int.castRingHom F) = PaperP1.FormalWordPolynomials.linearOver F I := by
  simp only [linear, PaperP1.FormalWordPolynomials.linearOver, Polynomial.map_prod,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rfl

theorem radicand_map (F : Type*) [Field F] (c : ℤ) (I J : Finset ℤ) :
    coefficientMap F (radicand c I J) = PaperP1.ScaledSplitWordSquares.scaledPolynomial (c : F) I J := by
  let φ : ℤ →+* F := Int.castRingHom F
  let ψ : ℤ[X] →+* F[X] := Polynomial.mapRingHom φ
  have hcomp : ψ.comp (C : ℤ →+* ℤ[X]) = (C : F →+* F[X]).comp φ := by
    apply RingHom.ext
    intro a
    exact Polynomial.map_C φ
  have hc : ψ (C c) = C (c : F) := Polynomial.map_C φ
  have hlinear (S : Finset ℤ) : ψ (linear S) = PaperP1.FormalWordPolynomials.linearOver F S := linear_map F S
  change (C (C c) * (C (linear I) * (linear J).map C)).map ψ =
    C (C (c : F)) * (C (PaperP1.FormalWordPolynomials.linearOver F I) *
      (PaperP1.FormalWordPolynomials.linearOver F J).map C)
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hc, hlinear,
    Polynomial.map_map, hcomp, ← Polynomial.map_map]
  have he : (linear J).map φ = PaperP1.FormalWordPolynomials.linearOver F J := linear_map F J
  rw [he]

theorem equations_map {ι : Type*} (F : Type*) [Field F] (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) :
    (equations l c I J).map (coefficientMap F) =
      PaperP1.SplitRadicalCoordinateAlgebra.radicands l (fun i ↦ (c i : F)) I J := by
  simp only [equations, PaperP1.SplitRadicalCoordinateAlgebra.radicands, List.map_map, Function.comp_def,
    radicand_map]

def sourceMap {ι : Type*} (F : Type*) [Field F] (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) :
    Source l c I J →+* PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra l (fun i ↦ (c i : F)) I J :=
  (PaperP1.QuadraticTowerListCongr.congr F[X][X] (equations_map F l c I J)).toRingHom.comp
    (PaperP1.QuadraticTowerBaseChange.mapData (coefficientMap F) (equations l c I J)).hom

theorem sourceMap_base {ι : Type*} (F : Type*) [Field F] (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ)
    (P : ℤ[X][X]) :
    sourceMap F l c I J (algebraMap ℤ[X][X] (Source l c I J) P) =
      algebraMap F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra l (fun i ↦ (c i : F)) I J)
        (coefficientMap F P) := by
  change PaperP1.QuadraticTowerListCongr.congr F[X][X] (equations_map F l c I J)
    ((PaperP1.QuadraticTowerBaseChange.mapData (coefficientMap F) (equations l c I J)).hom
      (algebraMap ℤ[X][X] (Source l c I J) P)) = _
  rw [PaperP1.QuadraticTowerBaseChange.MapData.commutes, PaperP1.QuadraticTowerListCongr.congr_base]

theorem sourceMap_root {ι : Type*} (F : Type*) [Field F] (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ)
    (i : Fin (equations l c I J).length) :
    sourceMap F l c I J (root ℤ[X][X] (equations l c I J) i) =
      root F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.radicands l (fun i ↦ (c i : F)) I J)
        ⟨i.val, by simpa only [equations, PaperP1.SplitRadicalCoordinateAlgebra.radicands, List.length_map] using i.isLt⟩ := by
  change PaperP1.QuadraticTowerListCongr.congr F[X][X] (equations_map F l c I J)
    ((PaperP1.QuadraticTowerBaseChange.mapData (coefficientMap F) (equations l c I J)).hom
      (root ℤ[X][X] (equations l c I J) i)) = _
  rw [PaperP1.QuadraticTowerGeneratorBaseChange.map_root, PaperP1.QuadraticTowerListCongr.congr_root]

end PaperP1.IntegralSplitRadicalModel
