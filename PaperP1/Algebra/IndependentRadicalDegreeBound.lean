module

public import PaperP1.Algebra.IndependentQuadraticTower
public import PaperP1.Algebra.QuadraticTowerPoints
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Independent square roots force an actual power of two to divide the extension degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentRadicalDegreeBound

open PaperP1.FiniteQuadraticTower

variable {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]

theorem lift_injective (s : List K) (hs : IndependentQuadraticTower.Independent s)
    (r : Fin s.length → E) (hr : ∀ i, r i ^ 2 = algebraMap K E (s.get i)) :
    Function.Injective (QuadraticTowerPoints.lift K E s r hr) := by
  let : Field (Tower K s) := (IndependentQuadraticTower.isField K s hs).toField
  exact (QuadraticTowerPoints.lift K E s r hr).toRingHom.injective

theorem power_dvd_degree (s : List K) (hs : IndependentQuadraticTower.Independent s)
    (r : Fin s.length → E) (hr : ∀ i, r i ^ 2 = algebraMap K E (s.get i)) :
    2 ^ s.length ∣ Module.finrank K E := by
  let : Field (Tower K s) := (IndependentQuadraticTower.isField K s hs).toField
  let φ := QuadraticTowerPoints.lift K E s r hr
  let : Algebra (Tower K s) E := φ.toRingHom.toAlgebra
  have : IsScalarTower K (Tower K s) E := IsScalarTower.of_algebraMap_eq (fun a ↦ (φ.commutes a).symm)
  have h := Module.finrank_dvd_finrank_right K (Tower K s) E
  rw [FiniteQuadraticTower.finrank] at h
  exact h

theorem power_le_degree [Module.Finite K E] (s : List K) (hs : IndependentQuadraticTower.Independent s)
    (r : Fin s.length → E) (hr : ∀ i, r i ^ 2 = algebraMap K E (s.get i)) :
    2 ^ s.length ≤ Module.finrank K E :=
  Nat.le_of_dvd Module.finrank_pos (power_dvd_degree s hs r hr)

theorem not_all_squares [Module.Finite K E] (s : List K) (hs : IndependentQuadraticTower.Independent s)
    (hlarge : Module.finrank K E < 2 ^ s.length) :
    ¬ ∀ i : Fin s.length, IsSquare (algebraMap K E (s.get i)) := by
  intro hall
  choose r hr using hall
  have hroot (i : Fin s.length) : r i ^ 2 = algebraMap K E (s.get i) := by
    simpa only [pow_two] using (hr i).symm
  exact Nat.not_le_of_gt hlarge (power_le_degree s hs r hroot)

end PaperP1.IndependentRadicalDegreeBound
