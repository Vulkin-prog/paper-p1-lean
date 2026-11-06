module

public import PaperP1.Arithmetic.SplitRadicalAlgebraPointCount

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SplitRadicalCanonicalPointCount
open Polynomial Finset PaperP1.FiniteQuadraticTower PaperP1.SplitRadicalCoordinateAlgebra
open PaperP1.SplitRadicalFiniteFieldPointCount
open scoped Classical
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra
variable {F : Type*} [Field F] (k : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ)

def branchIndex : Fin (radicands (List.finRange k) c I J).length ≃ Fin k :=
  finCongr (by simp only [radicands, List.length_map, List.length_finRange])

theorem radicands_entry (i : Fin (radicands (List.finRange k) c I J).length) :
    (radicands (List.finRange k) c I J).get i =
      PaperP1.ScaledSplitWordSquares.scaledPolynomial (c (branchIndex k c I J i))
        (I (branchIndex k c I J i)) (J (branchIndex k c I J i)) := by
  change ((List.finRange k).map (fun j : Fin k ↦
    PaperP1.ScaledSplitWordSquares.scaledPolynomial (c j) (I j) (J j)))[i.val] = _
  rw [List.getElem_map, List.getElem_finRange]
  rfl

variable [Fintype F]

def concreteEquiv :
    PaperP1.BivariateQuadraticTowerPoints.Point (radicands (List.finRange k) c I J) ≃
      {v // v ∈ points c I J} where
  toFun v := ⟨(v.val.1, fun i ↦ v.val.2 ((branchIndex k c I J).symm i)), by
    apply (mem_points_iff c I J _).mpr
    intro i
    have ht := v.property ((branchIndex k c I J).symm i)
    rw [radicands_entry, Equiv.apply_symm_apply] at ht
    exact ht⟩
  invFun v := ⟨(v.val.1, fun i ↦ v.val.2 (branchIndex k c I J i)), by
    intro i
    rw [radicands_entry]
    exact (mem_points_iff c I J _).mp v.property (branchIndex k c I J i)⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext rfl
    exact funext (fun i ↦ congrArg v.val.2 ((branchIndex k c I J).symm_apply_apply i))
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext rfl
    exact funext (fun i ↦ congrArg v.val.2 ((branchIndex k c I J).apply_symm_apply i))

def pointsEquiv : (CoordinateAlgebra (List.finRange k) c I J →ₐ[F] F) ≃ {v // v ∈ points c I J} :=
  (PaperP1.BivariateQuadraticTowerPoints.pointsEquiv _).trans (concreteEquiv k c I J)

theorem cardinality : Nat.card (CoordinateAlgebra (List.finRange k) c I J →ₐ[F] F) =
    (points c I J).card :=
  (Nat.card_congr (pointsEquiv k c I J)).trans (Nat.card_eq_finsetCard (points c I J))

end PaperP1.SplitRadicalCanonicalPointCount
