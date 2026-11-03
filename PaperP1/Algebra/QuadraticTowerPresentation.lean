module

public import PaperP1.Algebra.QuadraticTowerPoints
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The literal multiradical polynomial quotient represents the constructed tower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerPresentation

open PaperP1.FiniteQuadraticTower

variable (R : Type*) [CommRing R] (s : List R)

abbrev PresentationRing := MvPolynomial (Fin s.length) R

def relation (i : Fin s.length) : PresentationRing R s :=
  MvPolynomial.X i ^ 2 - MvPolynomial.C (s.get i)

def relationIdeal : Ideal (PresentationRing R s) := Ideal.span (Set.range (relation R s))

abbrev Presentation := PresentationRing R s ⧸ relationIdeal R s

def evaluation : PresentationRing R s →ₐ[R] Tower R s := MvPolynomial.aeval (root R s)

theorem evaluation_X (i : Fin s.length) : evaluation R s (MvPolynomial.X i) = root R s i :=
  MvPolynomial.aeval_X _ _

theorem relation_evaluates (i : Fin s.length) : evaluation R s (relation R s i) = 0 := by
  simp only [evaluation, relation, map_sub, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    root_square, sub_self]

theorem relationIdeal_le_ker : relationIdeal R s ≤ RingHom.ker (evaluation R s).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact relation_evaluates R s i

def toTower : Presentation R s →ₐ[R] Tower R s :=
  Ideal.Quotient.liftₐ (relationIdeal R s) (evaluation R s) (fun _ hp ↦ relationIdeal_le_ker R s hp)

theorem toTower_mk (p : PresentationRing R s) :
    toTower R s (Ideal.Quotient.mk (relationIdeal R s) p) = evaluation R s p :=
  Ideal.Quotient.lift_mk _ _ _

def generator (i : Fin s.length) : Presentation R s :=
  Ideal.Quotient.mk (relationIdeal R s) (MvPolynomial.X i)

theorem generator_square (i : Fin s.length) :
    generator R s i ^ 2 = algebraMap R (Presentation R s) (s.get i) := by
  have hh : Ideal.Quotient.mk (relationIdeal R s) (relation R s i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change Ideal.Quotient.mk (relationIdeal R s) (MvPolynomial.X i) ^ 2 =
    Ideal.Quotient.mk (relationIdeal R s) (MvPolynomial.C (s.get i))
  simpa only [relation, map_sub, map_pow, sub_eq_zero] using hh

def fromTower : Tower R s →ₐ[R] Presentation R s :=
  QuadraticTowerPoints.lift R (Presentation R s) s (generator R s) (generator_square R s)

theorem fromTower_root (i : Fin s.length) : fromTower R s (root R s i) = generator R s i :=
  QuadraticTowerPoints.lift_root R _ s _ _ i

theorem toTower_generator (i : Fin s.length) : toTower R s (generator R s i) = root R s i := by
  rw [generator, toTower_mk, evaluation_X]

theorem toTower_comp_fromTower :
    (toTower R s).comp (fromTower R s) = AlgHom.id R (Tower R s) := by
  apply QuadraticTowerPoints.hom_ext
  intro i
  change toTower R s (fromTower R s (root R s i)) = root R s i
  rw [fromTower_root, toTower_generator]

theorem fromTower_comp_toTower :
    (fromTower R s).comp (toTower R s) = AlgHom.id R (Presentation R s) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fromTower R s (toTower R s (generator R s i)) = generator R s i
  rw [toTower_generator, fromTower_root]

def presentationEquiv : Presentation R s ≃ₐ[R] Tower R s :=
  AlgEquiv.ofAlgHom (toTower R s) (fromTower R s)
    (toTower_comp_fromTower R s) (fromTower_comp_toTower R s)

theorem presentationEquiv_generator (i : Fin s.length) :
    presentationEquiv R s (generator R s i) = root R s i := toTower_generator R s i

theorem ker_evaluation : RingHom.ker (evaluation R s).toRingHom = relationIdeal R s := by
  apply le_antisymm _ (relationIdeal_le_ker R s)
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (presentationEquiv R s).injective
  change toTower R s (Ideal.Quotient.mk (relationIdeal R s) p) = _
  rw [toTower_mk, map_zero]
  exact hp

theorem presentation_isDomain (h : IsDomain (Tower R s)) : IsDomain (Presentation R s) := by
  let := h
  exact (presentationEquiv R s).injective.isDomain (presentationEquiv R s).toRingHom

end PaperP1.QuadraticTowerPresentation
