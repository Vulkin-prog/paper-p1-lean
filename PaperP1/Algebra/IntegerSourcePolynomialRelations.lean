module

public import PaperP1.Algebra.IntegralSplitRadicalReduction
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Every actual integral polynomial relation detected in the faithful rational source reduces to every field -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegerSourcePolynomialRelations
open Polynomial Finset IntegralSplitRadicalModel IntegralSplitRadicalReduction
open scoped Classical

theorem map_integer_evaluation {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (v : σ → R) (P : MvPolynomial σ ℤ) :
    φ (MvPolynomial.eval₂ (Int.castRingHom R) v P) =
      MvPolynomial.eval₂ (Int.castRingHom S) (fun i ↦ φ (v i)) P := by
  have hc : φ.comp (Int.castRingHom R) = Int.castRingHom S := Subsingleton.elim _ _
  have hh := MvPolynomial.map_eval₂Hom (Int.castRingHom R) v φ P
  rw [hc] at hh
  exact hh

theorem integer_evaluation_eq_mapped_aeval {σ F A : Type*} [Field F] [CommRing A] [Algebra F A]
    (v : σ → A) (P : MvPolynomial σ ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom A) v P =
      MvPolynomial.aeval (R := F) v (MvPolynomial.map (Int.castRingHom F) P) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  have hc : (algebraMap F A).comp (Int.castRingHom F) = Int.castRingHom A := Subsingleton.elim _ _
  rw [hc]

theorem integer_relation_transfer {ι σ : Type*} (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ)
    (v : σ → Source l c I J) (P : MvPolynomial σ ℤ)
    (hQ : MvPolynomial.eval₂ (Int.castRingHom (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra l (fun i ↦ (c i : ℚ)) I J))
      (fun i ↦ sourceMap ℚ l c I J (v i)) P = 0) (F : Type*) [Field F] :
    MvPolynomial.eval₂ (Int.castRingHom (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra l (fun i ↦ (c i : F)) I J))
      (fun i ↦ sourceMap F l c I J (v i)) P = 0 := by
  let a : Source l c I J := MvPolynomial.eval₂ (Int.castRingHom _) v P
  have haQ : sourceMap ℚ l c I J a = 0 := (map_integer_evaluation (sourceMap ℚ l c I J) v P).trans hQ
  have ha := relation_reduces l c I J a haQ F
  rw [map_integer_evaluation] at ha
  exact ha

end PaperP1.IntegerSourcePolynomialRelations
