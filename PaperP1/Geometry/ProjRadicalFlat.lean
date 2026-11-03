module

public import PaperP1.Geometry.ProjRadicalCharts
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness of the actual radical-admissible projective map from its degree-one charts -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjRadicalFlat

open AlgebraicGeometry CategoryTheory HomogeneousLocalization AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

theorem restriction_flat {b : A} (hb : b ∈ G 1) (hflat : (Away.map f b).Flat) :
    Flat ((ProjRadicalMap.map f hf).resLE (basicOpen G b) (basicOpen H (f b)) le_rfl) := by
  have : Flat (Spec.map (CommRingCat.ofHom (Away.map f b))) := Flat.SpecMap_iff.mpr hflat
  rw [ProjRadicalCharts.restriction_eq f hf hb]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem map_flat
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range fun b : G 1 ↦ (b : A)))
    (hflat : ∀ b : G 1, (Away.map f (b : A)).Flat) : Flat (ProjRadicalMap.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @Flat.{u})
    (f := ProjRadicalMap.map f hf) (fun b : G 1 ↦ basicOpen G (b : A))
    (Proj.iSup_basicOpen_eq_top G (fun b : G 1 ↦ (b : A)) hcover)]
  intro b
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  change Flat ((ProjRadicalMap.map f hf).resLE (basicOpen G (b : A))
    (basicOpen H (f (b : A))) le_rfl)
  exact restriction_flat f hf b.property (hflat b)

end PaperP1.ProjRadicalFlat
