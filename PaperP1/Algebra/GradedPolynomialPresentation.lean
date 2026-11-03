module

public import PaperP1.Algebra.GradedPolynomialGenerators
public import PaperP1.Algebra.GradedSurjectiveChartMap
public import PaperP1.Algebra.WeightedPolynomialQuotientGrading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # The actual homogeneous coordinate quotient and all its graded pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedPolynomialPresentation

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F A ι : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (H : ℕ → Submodule F A) [GradedAlgebra H] (g : ι → A)
  (hg : ∀ i, g i ∈ H 1) (hgen : Algebra.adjoin F (Set.range g) = ⊤)

def kernel : Ideal (MvPolynomial ι F) := RingHom.ker (MvPolynomial.aeval g)

include hg in
theorem kernel_homogeneous : (kernel (F := F) g).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι F) := by
  have h := ((⊥ : HomogeneousIdeal H).comap (GradedPolynomialGenerators.gradedEval H g hg)).isHomogeneous
  change (kernel (F := F) g).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι F) at h
  exact h

abbrev CoordinateRing := MvPolynomial ι F ⧸ kernel (F := F) g

def toSource : CoordinateRing (F := F) g ≃ₐ[F] A :=
  Ideal.quotientKerAlgEquivOfSurjective
    (show Function.Surjective (MvPolynomial.aeval g) from
      GradedPolynomialGenerators.eval_surjective H g hg hgen)

theorem toSource_mk (p : MvPolynomial ι F) :
    toSource H g hg hgen (Ideal.Quotient.mk (kernel (F := F) g) p) = MvPolynomial.aeval g p :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ p

def piece (n : ℕ) : Submodule F (CoordinateRing (F := F) g) :=
  (MvPolynomial.homogeneousSubmodule ι F n).map (Ideal.Quotient.mkₐ F (kernel (F := F) g)).toLinearMap

@[instance_reducible] def grading : GradedAlgebra (piece (F := F) g) :=
  WeightedPolynomialQuotientGrading.gradedAlgebra (1 : ι → ℕ) (kernel (F := F) g)
    (kernel_homogeneous H g hg)

theorem piece_map (n : ℕ) : (piece (F := F) g n).map (toSource H g hg hgen).toLinearMap = H n := by
  rw [piece, ← Submodule.map_comp]
  have he : (toSource H g hg hgen).toLinearMap.comp (Ideal.Quotient.mkₐ F (kernel (F := F) g)).toLinearMap =
      (MvPolynomial.aeval g).toLinearMap := by
    apply LinearMap.ext
    intro p
    exact toSource_mk H g hg hgen p
  rw [he]
  apply le_antisymm
  · rintro y ⟨p, hp, rfl⟩
    exact GradedPolynomialGenerators.eval_homogeneous H g hg n p hp
  · intro y hy
    obtain ⟨p, hp, hpy⟩ := GradedSurjectiveChartMap.homogeneous_preimage
      (GradedPolynomialGenerators.gradedEval H g hg)
      (GradedPolynomialGenerators.eval_surjective H g hg hgen) n y hy
    exact ⟨p, hp, hpy⟩

def pieceEquiv (n : ℕ) : piece (F := F) g n ≃ₗ[F] H n :=
  (toSource H g hg hgen).toLinearEquiv.ofSubmodules (piece (F := F) g n) (H n) (piece_map H g hg hgen n)

theorem pieceEquiv_apply (n : ℕ) (x : piece (F := F) g n) :
    (pieceEquiv H g hg hgen n x : A) = toSource H g hg hgen x :=
  LinearEquiv.ofSubmodules_apply _ _ _

end PaperP1.GradedPolynomialPresentation
