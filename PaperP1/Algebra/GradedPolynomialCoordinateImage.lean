module

public import PaperP1.Algebra.FiniteLinearCurveImageNormalization
public import PaperP1.Algebra.GradedPolynomialPresentation
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # An actual finite linear polynomial-coordinate image of a curve constructs its own quotient Hilbert polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedPolynomialCoordinateImage

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F R σ : Type*} [Field F] [CommRing R] [Algebra F R]

abbrev CoordinateRing (g : σ → R) := MvPolynomial σ F ⧸ RingHom.ker (MvPolynomial.aeval (R := F) g)

def piece (g : σ → R) (n : ℕ) : Submodule F (CoordinateRing (F := F) g) :=
  HomogeneousQuotientGrading.piece (MvPolynomial.homogeneousSubmodule σ F)
    (RingHom.ker (MvPolynomial.aeval (R := F) g)) n

def toSource (g : σ → R) : CoordinateRing (F := F) g →ₐ[F] R :=
  Ideal.kerLiftAlg (MvPolynomial.aeval (R := F) g)

theorem toSource_mk (g : σ → R) (P : MvPolynomial σ F) :
    toSource (F := F) g (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (R := F) g P := rfl

theorem toSource_injective (g : σ → R) : Function.Injective (toSource (F := F) g) :=
  Ideal.kerLiftAlg_injective _

@[instance_reducible]
def grading (H : ℕ → Submodule F R) [GradedAlgebra H] (g : σ → R) (hg : ∀ i, g i ∈ H 1) :
    GradedAlgebra (piece (F := F) g) :=
  HomogeneousQuotientGrading.grading (MvPolynomial.homogeneousSubmodule σ F)
    (RingHom.ker (MvPolynomial.aeval (R := F) g)) (GradedPolynomialPresentation.kernel_homogeneous H g hg)

def gradedToSource (H : ℕ → Submodule F R) [GradedAlgebra H] (g : σ → R) (hg : ∀ i, g i ∈ H 1) :
    piece (F := F) g →+*ᵍ H where
  __ := (toSource (F := F) g).toRingHom
  map_mem hx := by
    obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hx
    exact GradedPolynomialGenerators.eval_homogeneous H g hg _ P hP

theorem exists_finite_parameters [Infinite F] [Finite σ]
    (H : ℕ → Submodule F R) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (a b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (g : σ → R) (hg : ∀ i, g i ∈ H 1) :
    ∃ u : Fin 2 → CoordinateRing (F := F) g,
      (∀ i, u i ∈ piece (F := F) g 1) ∧ (MvPolynomial.aeval (R := F) u).Finite := by
  classical
  let := Fintype.ofFinite σ
  let I := RingHom.ker (MvPolynomial.aeval (R := F) g)
  let := grading H g hg
  let e := (Fintype.equivFin σ).symm
  let v : Fin (Fintype.card σ) → CoordinateRing (F := F) g :=
    fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X (e i))
  have hv (i : Fin (Fintype.card σ)) : v i ∈ piece (F := F) g 1 :=
    Submodule.mem_map.mpr ⟨MvPolynomial.X (e i), MvPolynomial.isHomogeneous_X F _, rfl⟩
  have heval : MvPolynomial.aeval (R := F) v =
      (Ideal.Quotient.mkₐ F I).comp (MvPolynomial.rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, MvPolynomial.aeval_X]
    rfl
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := F) v) := by
    rw [heval]
    intro x
    have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    obtain ⟨P, hP⟩ := hmk x
    obtain ⟨Q, hQ⟩ := MvPolynomial.rename_surjective (R := F) e e.surjective P
    refine ⟨Q, ?_⟩
    change Ideal.Quotient.mk I (MvPolynomial.rename e Q) = x
    rw [hQ, hP]
  exact FiniteLinearCurveImageNormalization.exists_two_parameters (piece (F := F) g) H
    (gradedToSource H g hg) (fun r ↦ (toSource (F := F) g).commutes r) (toSource_injective (F := F) g)
    a b hp (Fintype.card σ) v hv (AlgHom.Finite.of_surjective _ hsurj)


theorem exists_hilbert_polynomial [Infinite F] [IsDomain R] [Finite σ]
    (H : ℕ → Submodule F R) [GradedAlgebra H] [∀ n, Module.Finite F (H n)]
    (a b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial H
      (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (g : σ → R) (hg : ∀ i, g i ∈ H 1) :
    ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (piece (F := F) g) p := by
  let : (RingHom.ker (MvPolynomial.aeval (R := F) g)).IsPrime := RingHom.ker_isPrime _
  let := grading H g hg
  let f := gradedToSource H g hg
  let (n : ℕ) : Module.Finite F (piece (F := F) g n) := Module.Finite.of_injective
    (GradedInjectiveHilbertComparison.pieceMap f (fun r ↦ (toSource (F := F) g).commutes r) n)
    (GradedInjectiveHilbertComparison.pieceMap_injective f (fun r ↦ (toSource (F := F) g).commutes r)
      (toSource_injective (F := F) g) n)
  obtain ⟨u, hu, hufinite⟩ := exists_finite_parameters H a b hp g hg
  exact TwoVariableGradedHilbert.exists_polynomial_of_finite (piece (F := F) g) u hu hufinite

end PaperP1.GradedPolynomialCoordinateImage
