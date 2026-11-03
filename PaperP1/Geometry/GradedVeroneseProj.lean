module

public import PaperP1.Algebra.GradedVeroneseInclusion
public import PaperP1.Geometry.ProjDegreeScalingCharts

/-! # The actual projective spectrum is invariant under a positive Veronese construction -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.GradedVeroneseProj

open AlgebraicGeometry CategoryTheory MorphismProperty

variable {F A : Type u} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)

def map :
    letI := GradedVeroneseGrading.grading G D hD
    Proj G ⟶ Proj (GradedVeroneseGrading.piece G D) := by
  let := GradedVeroneseGrading.grading G D hD
  exact ProjDegreeScalingMap.map D hD (GradedVeroneseInclusion.inclusion G D)
    (GradedVeroneseInclusion.irrelevant_le_radical G D hD)

set_option backward.isDefEq.respectTransparency false in
theorem map_isIso :
    letI := GradedVeroneseGrading.grading G D hD
    IsIso (map G D hD) := by
  let := GradedVeroneseGrading.grading G D hD
  have hspan : (HomogeneousIdeal.irrelevant (GradedVeroneseGrading.piece G D)).toIdeal ≤
      Ideal.span (Set.range (fun b : Σ i : PNat, GradedVeroneseGrading.piece G D i ↦
        (b.2 : GradedVeroneseAlgebra.veronese G D))) := by
    rw [HomogeneousIdeal.irrelevant_eq_span]
    apply Ideal.span_mono
    intro x hx
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hx
    obtain ⟨n, hn, hx⟩ := hx
    exact ⟨⟨⟨n, hn⟩, ⟨x, hx⟩⟩, rfl⟩
  change (isomorphisms Scheme) (map G D hD)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := isomorphisms Scheme) (f := map G D hD)
    (fun b : Σ i : PNat, GradedVeroneseGrading.piece G D i ↦
      Proj.basicOpen (GradedVeroneseGrading.piece G D) (b.2 : GradedVeroneseAlgebra.veronese G D))
    (Proj.iSup_basicOpen_eq_top (GradedVeroneseGrading.piece G D) _ hspan)]
  intro b
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  change IsIso ((ProjDegreeScalingMap.map D hD (GradedVeroneseInclusion.inclusion G D)
    (GradedVeroneseInclusion.irrelevant_le_radical G D hD)).resLE _ _ le_rfl)
  exact ProjDegreeScalingCharts.restriction_isIso D hD (GradedVeroneseInclusion.inclusion G D)
    (GradedVeroneseInclusion.irrelevant_le_radical G D hD) b.1.property b.2.property
    ⟨GradedVeroneseInclusion.chart_injective G D hD b.2,
      GradedVeroneseInclusion.chart_surjective G D hD b.2 b.2.property⟩

def iso :
    letI := GradedVeroneseGrading.grading G D hD
    Proj G ≅ Proj (GradedVeroneseGrading.piece G D) := by
  let := GradedVeroneseGrading.grading G D hD
  have : IsIso (map G D hD) := map_isIso G D hD
  exact asIso (map G D hD)

theorem iso_hom :
    letI := GradedVeroneseGrading.grading G D hD
    (iso G D hD).hom = map G D hD := rfl

end PaperP1.GradedVeroneseProj
