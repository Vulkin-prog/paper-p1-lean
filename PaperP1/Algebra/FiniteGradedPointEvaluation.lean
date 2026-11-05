module

public import PaperP1.Algebra.HomogeneousFiniteInterpolation
public import PaperP1.Algebra.MvPolynomialHilbert
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Actual normalized point populations are bounded by a homogeneous image dimension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteGradedPointEvaluation

open MvPolynomial

theorem card_le_dimension {F σ B : Type*} [Field F] [Finite σ] [CommRing B] [Algebra F B]
    (S : Finset (σ → F)) (z : σ) (hnormal : ∀ w ∈ S, w z = 1)
    (n : ℕ) (hn : S.card - 1 ≤ n) (q : MvPolynomial σ F →ₐ[F] B)
    (ev : S → B →ₐ[F] F) (heval : ∀ P : MvPolynomial σ F, ∀ w : S, ev w (q P) = eval w.val P) :
    S.card ≤ Module.finrank F ((homogeneousSubmodule σ F n).map q.toLinearMap) := by
  classical
  let G := (homogeneousSubmodule σ F n).map q.toLinearMap
  let : Module.Finite F (homogeneousSubmodule σ F n) := MvPolynomialHilbert.piece_finite F σ n
  let : Module.Finite F G := Module.Finite.map _ _
  have hex (i : S) := HomogeneousFiniteInterpolation.selector S z hnormal i.val i.property n hn
  choose f hf hvalue using hex
  let v : S → G := fun i ↦ ⟨q (f i), Submodule.mem_map.mpr ⟨f i, hf i, rfl⟩⟩
  let L : G →ₗ[F] (S → F) :=
    { toFun := fun b w ↦ ev w b.val
      map_add' := fun b c ↦ funext (fun w ↦ map_add (ev w) b.val c.val)
      map_smul' := fun a b ↦ funext (fun w ↦ (ev w).toLinearMap.map_smul a b.val) }
  have himage : L ∘ v = fun i : S ↦ Pi.single i (1 : F) := by
    funext i w
    change ev w (q (f i)) = (Pi.single i (1 : F) : S → F) w
    rw [heval, hvalue i w.val w.property]
    by_cases hwi : w = i
    · subst w
      simp
    · have hval : w.val ≠ i.val := fun he ↦ hwi (Subtype.ext he)
      rw [ite_eq_right hval, Pi.single_eq_of_ne hwi]
  have hbasis : (fun i : S ↦ Pi.single i (1 : F)) = (Pi.basisFun F S : S → S → F) := by
    funext i
    exact (Pi.basisFun_apply F S i).symm
  have hli : LinearIndependent F (L ∘ v) := by
    rw [himage, hbasis]
    exact (Pi.basisFun F S).linearIndependent
  have hc := (LinearIndependent.of_comp L hli).fintype_card_le_finrank
  simpa only [Fintype.card_coe] using hc

end PaperP1.FiniteGradedPointEvaluation
