module

public import PaperP1.Algebra.P3GraphPlaneKernel
public import PaperP1.Algebra.HomogeneousFactorDegrees
public import PaperP1.Diophantine.GraphPlaneCoarsePointCount
public import PaperP1.Algebra.AlgClosedPolynomialIrreducibility

/-! # One actual irreducible homogeneous graph-plane section certifies the original surface

This is the reflection direction. It does not assert that every geometrically
irreducible surface has such a section.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GraphPlaneIrreducibilityCertificate

open MvPolynomial P3GraphPlaneSection

variable {F : Type} [Field F]

theorem unit_of_homogeneous_section_unit (a : Fin 3 → F) (A : MvPolynomial (Fin 4) F)
    {e : ℕ} (hA : A.IsHomogeneous e) (hu : IsUnit (planeSection a A)) : IsUnit A := by
  have himage : planeSection a A ≠ 0 := hu.ne_zero
  have he : e = 0 := by
    have hh := (section_homogeneous a A hA).totalDegree himage
    have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have hA0 : A ≠ 0 := by
    intro hz
    exact himage (by rw [hz, map_zero])
  have hd : A.totalDegree = 0 := by rw [hA.totalDegree hA0, he]
  have hc : A.coeff 0 ≠ 0 := by
    intro hz
    apply hA0
    rw [totalDegree_eq_zero_iff_eq_C.mp hd, hz, map_zero]
  rw [totalDegree_eq_zero_iff_eq_C.mp hd]
  exact (isUnit_iff_ne_zero.mpr hc).map C

theorem irreducible_of_section (P : MvPolynomial (Fin 4) F) {d : ℕ}
    (hP : P.IsHomogeneous d) (a : Fin 3 → F) (hirr : Irreducible (planeSection a P)) :
    Irreducible P := by
  have hP0 : P ≠ 0 := by
    intro hz
    exact hirr.ne_zero (by rw [hz, map_zero])
  refine ⟨fun hu ↦ hirr.not_isUnit (hu.map (planeSection a)), ?_⟩
  intro A B hAB
  have hAB0 : A * B ≠ 0 := by rw [← hAB]; exact hP0
  obtain ⟨hA, hB⟩ := HomogeneousFactorDegrees.homogeneous_factors A B hAB0 d (hAB ▸ hP)
  have he : planeSection a P = planeSection a A * planeSection a B := by rw [hAB, map_mul]
  rcases hirr.isUnit_or_isUnit he with hu | hu
  · exact Or.inl (unit_of_homogeneous_section_unit a A hA hu)
  · exact Or.inr (unit_of_homogeneous_section_unit a B hB hu)

theorem geometric_irreducible_of_section (P : MvPolynomial (Fin 4) F) {d : ℕ}
    (hP : P.IsHomogeneous d) (a : Fin 3 → AlgebraicClosure F)
    (hirr : Irreducible (planeSection a (map (algebraMap F (AlgebraicClosure F)) P))) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) P) :=
  irreducible_of_section _ (hP.map _) a hirr

theorem geometric_irreducible_of_geometric_section (P : MvPolynomial (Fin 4) F) {d : ℕ}
    (hP : P.IsHomogeneous d) (a : Fin 3 → F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) (planeSection a P))) :
    Irreducible (map (algebraMap F (AlgebraicClosure F)) P) := by
  apply geometric_irreducible_of_section P hP (fun i ↦ algebraMap F (AlgebraicClosure F) (a i))
  change Irreducible (planeSection ((algebraMap F (AlgebraicClosure F)) ∘ a)
    (map (algebraMap F (AlgebraicClosure F)) P))
  rw [← GraphPlaneCoarsePointCount.map_section]
  exact hirr

end PaperP1.P3GraphPlaneIrreducibilityCertificate
