module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Algebra.Tower

/-! # An injective intermediate algebra of a finite algebra is finite over a Noetherian base -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteInjectiveIntermediate

theorem finite_factor {F R B A : Type*} [CommRing F] [CommRing R] [CommRing B] [CommRing A]
    [Algebra F R] [Algebra F B] [Algebra F A] [IsNoetherianRing R]
    (p : R →ₐ[F] B) (f : B →ₐ[F] A) (hinj : Function.Injective f)
    (hfinite : (f.comp p).Finite) : p.Finite := by
  let : Algebra R B := p.toRingHom.toAlgebra
  let : Algebra B A := f.toRingHom.toAlgebra
  let : Algebra R A := (f.comp p).toRingHom.toAlgebra
  let : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let : Module.Finite R A := hfinite
  change Module.Finite R B
  exact Module.Finite.of_injective (IsScalarTower.toAlgHom R B A).toLinearMap hinj

end PaperP1.FiniteInjectiveIntermediate
