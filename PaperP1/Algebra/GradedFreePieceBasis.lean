module

public import PaperP1.Algebra.HomogeneousPieceBasis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-! # Actual vector bases and homogeneous pieces of a free graded algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedFreePieceBasis

open Module

variable {F A B ι κ : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B} [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (eA : Basis ι F A) (eB : letI : Algebra A B := f.toRingHom.toAlgebra; Basis κ A B)

def basis : Basis (ι × κ) F B := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq (fun a ↦ (hscalar a).symm)
  exact eA.smulTower eB

omit [GradedAlgebra H] in
theorem basis_apply (i : ι × κ) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    basis f hscalar eA eB i = eA i.1 • eB i.2 := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have : IsScalarTower F A B := IsScalarTower.of_algebraMap_eq (fun a ↦ (hscalar a).symm)
  exact Basis.smulTower_apply eA eB i

variable (wA : ι → ℕ) (wB : κ → ℕ)
  (hA : ∀ i, eA i ∈ G (wA i)) (hB : ∀ j, eB j ∈ H (wB j))

include hA hB in
theorem basis_mem (i : ι × κ) : basis f hscalar eA eB i ∈ H (wA i.1 + wB i.2) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  rw [basis_apply]
  change f (eA i.1) * eB i.2 ∈ H (wA i.1 + wB i.2)
  exact SetLike.mul_mem_graded (f.map_mem (hA i.1)) (hB i.2)

def pieceBasis (n : ℕ) : Basis {i : ι × κ // wA i.1 + wB i.2 = n} F (H n) :=
  HomogeneousPieceBasis.pieceBasis H (basis f hscalar eA eB) (fun i ↦ wA i.1 + wB i.2)
    (basis_mem f hscalar eA eB wA wB hA hB) n

theorem pieceBasis_apply (n : ℕ) (i : {i : ι × κ // wA i.1 + wB i.2 = n}) :
    (pieceBasis f hscalar eA eB wA wB hA hB n i : B) = basis f hscalar eA eB i.1 := by
  exact HomogeneousPieceBasis.pieceBasis_apply H (basis f hscalar eA eB) (fun i ↦ wA i.1 + wB i.2)
    (basis_mem f hscalar eA eB wA wB hA hB) n i

end PaperP1.GradedFreePieceBasis
