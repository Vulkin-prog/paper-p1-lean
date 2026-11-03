module

public import PaperP1.Geometry.ProjRadicalCharts
public import PaperP1.Algebra.GradedSurjectiveChartMap
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A surjective homogeneous presentation induces the actual closed immersion on Proj -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjSurjectiveClosedImmersion

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hsurj : Function.Surjective f)

include hsurj

theorem restriction_closedImmersion {b : A} (hb : b ∈ G 1) :
    IsClosedImmersion ((ProjRadicalMap.map f hf).resLE (Proj.basicOpen G b) (Proj.basicOpen H (f b)) le_rfl) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f b))) :=
    IsClosedImmersion.spec_of_surjective _ (GradedSurjectiveChartMap.away_map_surjective f hsurj hb)
  rw [ProjRadicalCharts.restriction_eq f hf hb]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem map_closedImmersion
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range fun b : G 1 ↦ (b : A))) :
    IsClosedImmersion (ProjRadicalMap.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion.{u}) (f := ProjRadicalMap.map f hf)
    (fun b : G 1 ↦ Proj.basicOpen G (b : A))
    (Proj.iSup_basicOpen_eq_top G (fun b : G 1 ↦ (b : A)) hcover)]
  intro b
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  change IsClosedImmersion ((ProjRadicalMap.map f hf).resLE
    (Proj.basicOpen G (b : A)) (Proj.basicOpen H (f (b : A))) le_rfl)
  exact restriction_closedImmersion f hf hsurj b.property

end PaperP1.ProjSurjectiveClosedImmersion
