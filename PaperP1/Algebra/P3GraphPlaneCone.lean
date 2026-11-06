module

public import PaperP1.Algebra.P3GraphPlaneSection
public import PaperP1.Algebra.IrreducibleVariableExtension
public import PaperP1.Arithmetic.P3GraphPlaneBadSectionCount

/-! # Every graph-plane section of a cone in the omitted coordinate is the actual defining plane curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneCone

open MvPolynomial P3GraphPlaneSection
open scoped Classical

theorem section_rename {F : Type*} [CommRing F] (a : Fin 3 → F) (Q : MvPolynomial (Fin 3) F) :
    planeSection a (rename Fin.succ Q) = Q := by
  have he : (planeSection a).comp (rename Fin.succ).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [planeSection]
    · intro i
      simp [planeSection, coordinates]
  exact RingHom.congr_fun he Q

theorem geometric_rename_iff {F : Type*} [Field F] (Q : MvPolynomial (Fin 3) F) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) (rename Fin.succ Q)) ↔
      Irreducible (map (algebraMap F (AlgebraicClosure F)) Q) := by
  rw [map_rename]
  exact IrreducibleVariableExtension.irreducible_rename Fin.succ (Fin.succ_injective 3) _

theorem all_sections_good {F : Type*} [Field F] (Q : MvPolynomial (Fin 3) F)
    (hgeom : Irreducible (map (algebraMap F (AlgebraicClosure F)) (rename Fin.succ Q)))
    (a : Fin 3 → F) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a (rename Fin.succ Q))) := by
  rw [section_rename]
  exact (geometric_rename_iff Q).mp hgeom

theorem bad_sections_empty {F : Type} [Field F] [Fintype F] (Q : MvPolynomial (Fin 3) F)
    (hgeom : Irreducible (map (algebraMap F (AlgebraicClosure F)) (rename Fin.succ Q))) :
    P3GraphPlaneBadSectionCount.badSections (rename Fin.succ Q) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact (Finset.mem_filter.mp ha).2 (all_sections_good Q hgeom a)

end PaperP1.P3GraphPlaneCone
