module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.Equiv

/-! # An irreducible relation of full degree forces a finite algebra to be a primitive field

The algebra need not initially be a domain. The degree comparison and the
actual polynomial relation produce the field equivalence and generation.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FullDegreePrimitiveAlgebra
open Polynomial Module
variable {K B : Type*} [Field K] [CommRing B] [Nontrivial B] [Algebra K B] [FiniteDimensional K B]

theorem exists_equiv (P : K[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : B) (hy : Polynomial.aeval y P = 0) (hdim : Module.finrank K B ≤ P.natDegree) :
    ∃ e : AdjoinRoot P ≃ₐ[K] B, e (AdjoinRoot.root P) = y := by
  let : Fact (Irreducible P) := ⟨hP⟩
  let : Module.Finite K (AdjoinRoot P) := hmonic.finite_adjoinRoot
  let f : AdjoinRoot P →ₐ[K] B := AdjoinRoot.liftAlgHom P (Algebra.ofId K B) y hy
  have hi : Function.Injective f := f.injective
  have hroot : Module.finrank K (AdjoinRoot P) = P.natDegree :=
    (AdjoinRoot.powerBasis (f := P) hP.ne_zero).finrank
  have hle := LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) hi
  have heq : Module.finrank K (AdjoinRoot P) = Module.finrank K B := by omega
  have hs : Function.Surjective f := by
    change Function.Surjective f.toLinearMap
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq ((LinearMap.finrank_range_of_inj hi).trans heq)
  refine ⟨AlgEquiv.ofBijective f ⟨hi, hs⟩, ?_⟩
  exact AdjoinRoot.liftAlgHom_root P (Algebra.ofId K B) y hy

theorem isField (P : K[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : B) (hy : Polynomial.aeval y P = 0) (hdim : Module.finrank K B ≤ P.natDegree) :
    IsField B := by
  obtain ⟨e, _⟩ := exists_equiv P hmonic hP y hy hdim
  exact MulEquiv.isField (AdjoinRoot.isField_iff_irreducible.mpr hP) e.symm.toMulEquiv

theorem adjoin_eq_top (P : K[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : B) (hy : Polynomial.aeval y P = 0) (hdim : Module.finrank K B ≤ P.natDegree) :
    Algebra.adjoin K ({y} : Set B) = ⊤ := by
  obtain ⟨e, he⟩ := exists_equiv P hmonic hP y hy hdim
  have hh := AlgHom.map_adjoin_singleton e.toAlgHom (AdjoinRoot.root P)
  have he' : e.toAlgHom (AdjoinRoot.root P) = y := he
  rw [AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top, he'] at hh
  exact hh.symm.trans ((AlgHom.range_eq_top e.toAlgHom).mpr e.surjective)

theorem finrank_eq (P : K[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (y : B) (hy : Polynomial.aeval y P = 0) (hdim : Module.finrank K B ≤ P.natDegree) :
    Module.finrank K B = P.natDegree := by
  obtain ⟨e, _⟩ := exists_equiv P hmonic hP y hy hdim
  exact e.toLinearEquiv.finrank_eq.symm.trans
    (AdjoinRoot.powerBasis (f := P) hP.ne_zero).finrank

end PaperP1.FullDegreePrimitiveAlgebra
