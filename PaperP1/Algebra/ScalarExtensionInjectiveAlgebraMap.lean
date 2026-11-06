module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Scalar extension preserves actual algebra injections and reflects domain structure along them -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScalarExtensionInjectiveAlgebraMap

open scoped TensorProduct

variable {F E A B : Type*} [Field F] [Field E] [Algebra F E]
  [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]

def map (E : Type*) [Field E] [Algebra F E] (f : A →ₐ[F] B) : E ⊗[F] A →ₐ[E] E ⊗[F] B :=
  Algebra.TensorProduct.map (AlgHom.id E E) f

theorem map_linear (f : A →ₐ[F] B) (t : E ⊗[F] A) :
    map E f t = f.toLinearMap.lTensor E t := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem injective (f : A →ₐ[F] B) (hf : Function.Injective f) : Function.Injective (map E f) := by
  have hi := Module.Flat.lTensor_preserves_injective_linearMap (M := E) f.toLinearMap hf
  intro a b hab
  apply hi
  simpa only [map_linear] using hab

theorem isDomain [IsDomain (E ⊗[F] B)] (f : A →ₐ[F] B) (hf : Function.Injective f) :
    IsDomain (E ⊗[F] A) := (injective f hf).isDomain (map E f).toRingHom

end PaperP1.ScalarExtensionInjectiveAlgebraMap
