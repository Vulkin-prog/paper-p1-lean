module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Field.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Actual field points are determined by generating coordinates and preserve mixed evaluation -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GeneratedThreeCoordinatePoints
open Polynomial Finset
open scoped Classical
variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]

theorem coordinates_injective {σ : Type*} (v : σ → A)
    (hgen : Algebra.adjoin F (Set.range v) = ⊤) :
    Function.Injective (fun φ : A →ₐ[F] F ↦ fun i ↦ φ (v i)) := by
  intro φ ψ he
  apply AlgHom.ext_of_adjoin_eq_top hgen
  rintro _ ⟨i, rfl⟩
  exact congrFun he i

theorem points_finite {σ : Type*} [Finite σ] [Finite F] (v : σ → A)
    (hgen : Algebra.adjoin F (Set.range v) = ⊤) : Finite (A →ₐ[F] F) :=
  Finite.of_injective _ (coordinates_injective v hgen)

theorem mixed_evaluation (v : Fin 2 → A) (z : A) (φ : A →ₐ[F] F)
    (P : (MvPolynomial (Fin 2) F)[X]) :
    φ (P.eval₂ (MvPolynomial.aeval v).toRingHom z) =
      P.eval₂ (MvPolynomial.eval (fun i ↦ φ (v i))) (φ z) := by
  have he : φ.toRingHom.comp (MvPolynomial.aeval v).toRingHom =
      MvPolynomial.eval (fun i ↦ φ (v i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change φ (MvPolynomial.aeval v (MvPolynomial.C r)) =
        MvPolynomial.eval (fun i ↦ φ (v i)) (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C, MvPolynomial.eval_C]
      exact φ.commutes r
    · intro i
      change φ (MvPolynomial.aeval v (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
  have hh := Polynomial.hom_eval₂ (p := P) (f := (MvPolynomial.aeval v).toRingHom) (g := φ.toRingHom) (x := z)
  rw [he] at hh
  exact hh

def values (v : Fin 2 → A) (z : A) (φ : A →ₐ[F] F) : (Fin 2 → F) × F :=
  (fun i ↦ φ (v i), φ z)

theorem values_injective (v : Fin 2 → A) (z : A)
    (hgen : Algebra.adjoin F (Set.range (Fin.cons z v)) = ⊤) : Function.Injective (values (F := F) v z) := by
  intro φ ψ he
  apply coordinates_injective (Fin.cons z v) hgen
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change φ z = ψ z
    exact congrArg Prod.snd he
  · change φ (v j) = ψ (v j)
    exact congrFun (congrArg Prod.fst he) j

end PaperP1.GeneratedThreeCoordinatePoints
