module

public import PaperP1.Algebra.QuadraticTowerRootBasis
public import PaperP1.Algebra.QuadraticTowerPoints
public import PaperP1.Algebra.FiniteRadicalProjection

/-! # The actual independent radical sign changes and their distinct sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerSigns

open Finset PaperP1.FiniteQuadraticTower PaperP1.QuadraticTowerRootBasis

def signScalar (R : Type*) [CommRing R] (b : Bool) : R := if b then -1 else 1

def signedRoot (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) (i : Fin s.length) : Tower R s :=
  signScalar R (ε i) • root R s i

theorem signed_square (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) (i : Fin s.length) :
    signedRoot R s ε i ^ 2 = algebraMap R (Tower R s) (s.get i) := by
  cases h : ε i <;> simp [signedRoot, signScalar, h, root_square]

def signHom (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) : Tower R s →ₐ[R] Tower R s :=
  QuadraticTowerPoints.lift R (Tower R s) s (signedRoot R s ε) (signed_square R s ε)

theorem sign_root (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) (i : Fin s.length) :
    signHom R s ε (root R s i) = signedRoot R s ε i := QuadraticTowerPoints.lift_root R (Tower R s) s _ _ i

theorem signHom_self (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) :
    (signHom R s ε).comp (signHom R s ε) = AlgHom.id R (Tower R s) := by
  apply QuadraticTowerPoints.hom_ext R (Tower R s) s
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, sign_root]
  cases h : ε i <;> simp [signedRoot, signScalar, h, map_neg, sign_root]

def signEquiv (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) : Tower R s ≃ₐ[R] Tower R s := by
  have hinv : Function.Involutive (signHom R s ε) := fun z ↦
    congrArg (fun φ : Tower R s →ₐ[R] Tower R s ↦ φ z) (signHom_self R s ε)
  exact AlgEquiv.ofBijective (signHom R s ε) hinv.bijective

theorem signEquiv_root (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) (i : Fin s.length) :
    signEquiv R s ε (root R s i) = signedRoot R s ε i := sign_root R s ε i

def signedSum (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) : Tower R s :=
  ∑ i : Fin s.length, signedRoot R s ε i

theorem map_radicalSum (R : Type*) [CommRing R] (s : List R) (ε : Fin s.length → Bool) :
    signHom R s ε (FiniteRadicalProjection.radicalSum R s) = signedSum R s ε := by
  rw [FiniteRadicalProjection.radicalSum, map_sum]
  exact sum_congr rfl (fun i _ ↦ sign_root R s ε i)

theorem signedSum_injective (R : Type*) [CommRing R] [CharZero R] (s : List R) :
    Function.Injective (signedSum R s) := by
  intro ε η heq
  have hsum : (∑ i : Fin s.length, signScalar R (ε i) • root R s i) =
      ∑ i : Fin s.length, signScalar R (η i) • root R s i := heq
  have hcoeff := (linearIndependent_iff'ₛ.mp (roots_linearlyIndependent R s)) univ
    (fun i ↦ signScalar R (ε i)) (fun i ↦ signScalar R (η i)) hsum
  funext i
  have hi := hcoeff i (mem_univ i)
  cases hε : ε i <;> cases hη : η i <;>
    first | rfl | norm_num [signScalar, hε, hη] at hi

def sumOrbit (R : Type*) [CommRing R] (s : List R) : Finset (Tower R s) := by
  classical
  exact univ.image (signedSum R s)

theorem sumOrbit_card (R : Type*) [CommRing R] [CharZero R] (s : List R) :
    (sumOrbit R s).card = 2 ^ s.length := by
  classical
  rw [sumOrbit, card_image_of_injective _ (signedSum_injective R s), card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end PaperP1.QuadraticTowerSigns
