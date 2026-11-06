module

public import PaperP1.Algebra.QuadraticTowerPoints
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.SetTheory.Cardinal.Finite

/-! # All field-valued points of a bivariate quadratic tower are the literal simultaneous solutions

Both base coordinates and every radical coordinate are recovered from the
actual scalar-preserving evaluation. The inverse is the proved universal map.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.BivariateQuadraticTowerPoints
open Polynomial PaperP1.FiniteQuadraticTower
variable {F : Type*} [Field F] (s : List F[X][X])
-- The scalar action is fixed through the literal tower base map.
@[instance_reducible]
def scalarAlgebra : Algebra F (Tower F[X][X] s) :=
  ((algebraMap F[X][X] (Tower F[X][X] s)).comp (algebraMap F F[X][X])).toAlgebra
attribute [local instance] scalarAlgebra

theorem scalarTower : IsScalarTower F F[X][X] (Tower F[X][X] s) :=
  IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
attribute [local instance] scalarTower
theorem base_evaluation (φ : Tower F[X][X] s →ₐ[F] F) (P : F[X][X]) :
    φ (algebraMap F[X][X] (Tower F[X][X] s) P) =
      P.evalEval (φ (algebraMap F[X][X] (Tower F[X][X] s) (C X)))
        (φ (algebraMap F[X][X] (Tower F[X][X] s) X)) := by
  let ρ := φ.toRingHom.comp (algebraMap F[X][X] (Tower F[X][X] s))
  let x : F := ρ (C X)
  let y : F := ρ X
  have hc : ρ.comp C = evalRingHom x := by
    apply Polynomial.ringHom_ext
    · intro r
      change φ (algebraMap F[X][X] (Tower F[X][X] s) (C (C r))) = (C r).eval x
      rw [eval_C]
      exact φ.commutes r
    · change x = X.eval x
      rw [eval_X]
  have he : ρ = evalEvalRingHom x y := by
    apply Polynomial.ringHom_ext
    · intro Q
      change ρ (C Q) = (C Q).evalEval x y
      rw [evalEval_C]
      exact DFunLike.congr_fun hc Q
    · change y = X.evalEval x y
      rw [evalEval_X]
  exact DFunLike.congr_fun he P

def evaluationRing (x y : F) (w : Fin s.length → F)
    (hw : ∀ i, w i ^ 2 = (s.get i).evalEval x y) : Tower F[X][X] s →+* F :=
  (PaperP1.QuadraticTowerPoints.unique_ringHom F[X][X] F (evalEvalRingHom x y) s w hw).choose

theorem evaluationRing_base (x y : F) (w : Fin s.length → F)
    (hw : ∀ i, w i ^ 2 = (s.get i).evalEval x y) (P : F[X][X]) :
    evaluationRing s x y w hw (algebraMap F[X][X] (Tower F[X][X] s) P) = P.evalEval x y :=
  (PaperP1.QuadraticTowerPoints.unique_ringHom F[X][X] F (evalEvalRingHom x y) s w hw).choose_spec.1.1 P

theorem evaluationRing_root (x y : F) (w : Fin s.length → F)
    (hw : ∀ i, w i ^ 2 = (s.get i).evalEval x y) (i : Fin s.length) :
    evaluationRing s x y w hw (root F[X][X] s i) = w i :=
  (PaperP1.QuadraticTowerPoints.unique_ringHom F[X][X] F (evalEvalRingHom x y) s w hw).choose_spec.1.2 i

def evaluation (x y : F) (w : Fin s.length → F)
    (hw : ∀ i, w i ^ 2 = (s.get i).evalEval x y) : Tower F[X][X] s →ₐ[F] F where
  toRingHom := evaluationRing s x y w hw
  commutes' r := by
    change evaluationRing s x y w hw (algebraMap F[X][X] (Tower F[X][X] s) (C (C r))) = r
    rw [evaluationRing_base, evalEval_CC]

theorem evaluation_base (x y : F) (w : Fin s.length → F)
    (hw : ∀ i, w i ^ 2 = (s.get i).evalEval x y) (P : F[X][X]) :
    evaluation s x y w hw (algebraMap F[X][X] (Tower F[X][X] s) P) = P.evalEval x y :=
  evaluationRing_base s x y w hw P

theorem evaluation_root (x y : F) (w : Fin s.length → F)
    (hw : ∀ i, w i ^ 2 = (s.get i).evalEval x y) (i : Fin s.length) :
    evaluation s x y w hw (root F[X][X] s i) = w i :=
  evaluationRing_root s x y w hw i

theorem hom_ext (φ ψ : Tower F[X][X] s →ₐ[F] F)
    (hx : φ (algebraMap F[X][X] (Tower F[X][X] s) (C X)) =
      ψ (algebraMap F[X][X] (Tower F[X][X] s) (C X)))
    (hy : φ (algebraMap F[X][X] (Tower F[X][X] s) X) =
      ψ (algebraMap F[X][X] (Tower F[X][X] s) X))
    (hw : ∀ i, φ (root F[X][X] s i) = ψ (root F[X][X] s i)) : φ = ψ := by
  apply AlgHom.ext
  intro z
  exact PaperP1.FiniteQuadraticTower.induction_on F[X][X] s (fun z ↦ φ z = ψ z)
    (fun P ↦ by rw [base_evaluation s φ P, base_evaluation s ψ P, hx, hy]) hw
    (fun a b ha hb ↦ by rw [map_add, map_add, ha, hb])
    (fun a b ha hb ↦ by rw [map_mul, map_mul, ha, hb]) z

def Point := {v : (F × F) × (Fin s.length → F) // ∀ i, v.2 i ^ 2 = (s.get i).evalEval v.1.1 v.1.2}

def coordinates (φ : Tower F[X][X] s →ₐ[F] F) : Point s :=
  ⟨((φ (algebraMap F[X][X] (Tower F[X][X] s) (C X)),
     φ (algebraMap F[X][X] (Tower F[X][X] s) X)), fun i ↦ φ (root F[X][X] s i)), by
    intro i
    rw [← map_pow, root_square, base_evaluation]⟩

def pointsEquiv : (Tower F[X][X] s →ₐ[F] F) ≃ Point s where
  toFun := coordinates s
  invFun v := evaluation s v.val.1.1 v.val.1.2 v.val.2 v.property
  left_inv φ := by
    apply hom_ext s
    · rw [evaluation_base, evalEval_C, eval_X]
      rfl
    · rw [evaluation_base, evalEval_X]
      rfl
    · intro i
      exact evaluation_root s _ _ _ _ i
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact (evaluation_base s _ _ _ _ (C X)).trans (by rw [evalEval_C, eval_X])
      · exact (evaluation_base s _ _ _ _ X).trans (by rw [evalEval_X])
    · exact funext (fun i ↦ evaluation_root s _ _ _ _ i)

theorem points_finite [Finite F] : Finite (Tower F[X][X] s →ₐ[F] F) := by
  have : Finite (Point s) := by unfold Point; infer_instance
  exact Finite.of_equiv (Point s) (pointsEquiv s).symm

theorem point_cardinality : Nat.card (Tower F[X][X] s →ₐ[F] F) = Nat.card (Point s) :=
  Nat.card_congr (pointsEquiv s)

end PaperP1.BivariateQuadraticTowerPoints
