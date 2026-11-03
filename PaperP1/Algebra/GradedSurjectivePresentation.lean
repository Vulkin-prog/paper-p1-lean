module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.GradedSurjectiveChartMap
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Algebra.Module.Submodule.Equiv

/-! # A surjective graded algebra map identifies its actual coordinate quotient and every graded piece -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedSurjectivePresentation

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B} [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hc : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (hf : Function.Surjective f)

def algebraHom : A →ₐ[F] B := { f.toRingHom with commutes' := hc }

abbrev CoordinateRing := A ⧸ RingHom.ker f.toRingHom

local instance quotientRing : CommRing (CoordinateRing f) := inferInstance
local instance quotientSemiring : Semiring (CoordinateRing f) := (quotientRing f).toSemiring
local instance quotientModule : Module F (CoordinateRing f) := Algebra.toModule

def piece (n : ℕ) : Submodule F (CoordinateRing f) :=
  HomogeneousQuotientGrading.piece G (RingHom.ker f.toRingHom) n

def toSource : CoordinateRing f ≃ₐ[F] B where
  __ := f.toRingHom.quotientKerEquivOfSurjective (show Function.Surjective f.toRingHom from hf)
  commutes' a := by
    change f.toRingHom.quotientKerEquivOfSurjective _
      (Ideal.Quotient.mk _ (algebraMap F A a)) = algebraMap F B a
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
    exact hc a

omit [GradedAlgebra G] [GradedAlgebra H] in
theorem toSource_mk (a : A) : toSource f hc hf (Ideal.Quotient.mk _ a) = f a :=
  RingHom.quotientKerEquivOfSurjective_apply_mk (f := f.toRingHom) hf a

theorem piece_map (n : ℕ) : (piece f n).map (toSource f hc hf).toLinearMap = H n := by
  rw [piece, HomogeneousQuotientGrading.piece, ← Submodule.map_comp]
  have he : (toSource f hc hf).toLinearMap.comp
      (Ideal.Quotient.mkₐ F (RingHom.ker f.toRingHom)).toLinearMap = (algebraHom f hc).toLinearMap := by
    apply LinearMap.ext
    intro a
    exact toSource_mk f hc hf a
  rw [he]
  apply le_antisymm
  · rintro y ⟨a, ha, rfl⟩
    exact f.map_mem ha
  · intro y hy
    obtain ⟨a, ha, hay⟩ := GradedSurjectiveChartMap.homogeneous_preimage f hf n y hy
    exact ⟨a, ha, hay⟩

def pieceEquiv (n : ℕ) : piece f n ≃ₗ[F] H n :=
  (toSource f hc hf).toLinearEquiv.ofSubmodules (piece f n) (H n) (piece_map f hc hf n)

section Hilbert

variable {K : Type*} [Field K] {C E : Type*} [CommRing C] [CommRing E] [Algebra K C] [Algebra K E]
  {G' : ℕ → Submodule K C} {H' : ℕ → Submodule K E} [GradedAlgebra G'] [GradedAlgebra H']
  (g : G' →+*ᵍ H') (hcomm : ∀ a : K, g (algebraMap K C a) = algebraMap K E a)
  (honto : Function.Surjective g)

include hcomm honto in
theorem piece_finrank (n : ℕ) : Module.finrank K (piece g n) = Module.finrank K (H' n) :=
  (pieceEquiv g hcomm honto n).finrank_eq

include hcomm honto in
theorem isHilbertPolynomial_iff (p : Polynomial ℚ) :
    GradedHilbertPolynomial.IsHilbertPolynomial (piece g) p ↔
      GradedHilbertPolynomial.IsHilbertPolynomial H' p := by
  constructor <;> rintro ⟨N, hN⟩ <;> refine ⟨N, fun n hn ↦ ?_⟩
  · rw [← piece_finrank g hcomm honto]
    exact hN n hn
  · rw [piece_finrank g hcomm honto]
    exact hN n hn

end Hilbert

end PaperP1.GradedSurjectivePresentation
