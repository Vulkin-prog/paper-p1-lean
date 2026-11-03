module

public import PaperP1.Algebra.GradedQuotientModuleGenerators
public import PaperP1.Algebra.GradedIrrelevantMap

/-! # The actual irrelevant-ideal bound descends to a target homogeneous quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientAdmissibility

variable {F A B : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H] (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (P : Ideal B) (hP : P.IsHomogeneous H)

include hf in
theorem irrelevant_le_radical :
    letI := HomogeneousQuotientGrading.grading G (GradedQuotientModuleGenerators.baseIdeal f P)
      (GradedQuotientModuleGenerators.baseIdeal_homogeneous f P hP)
    letI := HomogeneousQuotientGrading.grading H P hP
    (HomogeneousIdeal.irrelevant (HomogeneousQuotientGrading.piece H P)).toIdeal ≤
      ((HomogeneousIdeal.irrelevant
        (HomogeneousQuotientGrading.piece G (GradedQuotientModuleGenerators.baseIdeal f P))).toIdeal.map
          (GradedQuotientModuleGenerators.map f P).toRingHom).radical := by
  let I := GradedQuotientModuleGenerators.baseIdeal f P
  let := HomogeneousQuotientGrading.grading G I
    (GradedQuotientModuleGenerators.baseIdeal_homogeneous f P hP)
  let := HomogeneousQuotientGrading.grading H P hP
  let qA := HomogeneousQuotientGrading.mk G I
  let qB := HomogeneousQuotientGrading.mk H P
  let fbar := GradedQuotientModuleGenerators.map f P
  have hG := GradedIrrelevantMap.map_eq qA (HomogeneousQuotientGrading.mk_surjective G I)
  have hH := GradedIrrelevantMap.map_eq qB (HomogeneousQuotientGrading.mk_surjective H P)
  have hcomm : qB.toRingHom.comp f.toRingHom = fbar.toRingHom.comp qA.toRingHom := by
    apply RingHom.ext
    intro a
    rfl
  calc
    (HomogeneousIdeal.irrelevant (HomogeneousQuotientGrading.piece H P)).toIdeal =
        (HomogeneousIdeal.irrelevant H).toIdeal.map qB.toRingHom := hH.symm
    _ ≤ (((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical).map qB.toRingHom :=
      Ideal.map_mono hf
    _ ≤ (((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).map qB.toRingHom).radical :=
      Ideal.map_radical_le qB.toRingHom
    _ = (((HomogeneousIdeal.irrelevant G).toIdeal.map qA.toRingHom).map fbar.toRingHom).radical := by
      rw [Ideal.map_map, Ideal.map_map, hcomm]
    _ = _ := by rw [hG]

end PaperP1.GradedQuotientAdmissibility
