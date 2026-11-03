module

public import PaperP1.Algebra.FiniteQuadraticTower
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! # A faithful actual radical image has its literal free normal basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerImageBasis

open Module PaperP1.FiniteQuadraticTower

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (s : List R) (g : Tower R s →ₐ[R] A) (hg : Function.Injective g)

def imageBasis : Basis (Index s) R g.range :=
  (basis R s).map (AlgEquiv.ofInjective g hg).toLinearEquiv

theorem imageBasis_apply (i : Index s) : (imageBasis s g hg i : A) = g (basis R s i) := by
  rw [imageBasis, Basis.map_apply]
  rfl

include hg in
theorem image_free : Module.Free R g.range := .of_basis (imageBasis s g hg)

include hg in
theorem image_finite : Module.Finite R g.range := .of_basis (imageBasis s g hg)

include hg in
theorem image_finrank [Nontrivial R] : Module.finrank R g.range = 2 ^ s.length := by
  rw [Module.finrank_eq_card_basis (imageBasis s g hg), index_card]

theorem image_eq_adjoin : g.range = Algebra.adjoin R (Set.range fun i ↦ g (root R s i)) := by
  have hh := congrArg (fun S : Subalgebra R (Tower R s) ↦ S.map g) (adjoin_roots R s)
  rw [Algebra.map_top, ← Algebra.adjoin_image, ← Set.range_comp'] at hh
  exact hh.symm

end PaperP1.QuadraticTowerImageBasis
