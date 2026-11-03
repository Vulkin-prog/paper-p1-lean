/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

The first three chart compatibility proofs adapt
Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean,
Mathlib commit 9d581dfff2e41de989072ea63abf3daf69311520,
to PaperP1.ProjRadicalMap and its radical admissibility hypothesis.
-/
module

public import PaperP1.Geometry.ProjRadicalMap
public import PaperP1.Algebra.GradedDehomogenization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The actual radical-admissible Proj map on charts and its finiteness -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjRadicalCharts

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
  AlgebraicGeometry.ProjectiveSpectrum AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

set_option backward.isDefEq.respectTransparency.types false in
theorem inclusion_comp_map (b : A) :
    (basicOpen H (f b)).ι ≫ ProjRadicalMap.map f hf =
      (ProjRadicalMap.map f hf).resLE _ _ le_rfl ≫ (basicOpen G b).ι := by
  simp only [Scheme.Hom.resLE_comp_ι]
  rfl

theorem awayToSection_comp_appLE {i : ℕ} {b : A} (hb : b ∈ G i) :
    awayToSection G b ≫
      Scheme.Hom.appLE (ProjRadicalMap.map f hf) (basicOpen G b) (basicOpen H (f b)) (by rfl) =
    CommRingCat.ofHom (Away.map f b : Away G b →+* Away H (f b)) ≫ awayToSection H (f b) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hb
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
theorem chart_comp_map {i : ℕ} (hi : 0 < i) (b : A) (hb : b ∈ G i) :
    awayι H (f b) (f.map_mem hb) hi ≫ ProjRadicalMap.map f hf =
      Spec.map (CommRingCat.ofHom (Away.map f b)) ≫ awayι G b hb hi := by
  rw [awayι, awayι, Category.assoc, inclusion_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen H (f b)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE f hf hb]

set_option backward.isDefEq.respectTransparency false in
theorem restriction_eq {b : A} (hb : b ∈ G 1) :
    (ProjRadicalMap.map f hf).resLE (basicOpen G b) (basicOpen H (f b)) le_rfl =
      (basicOpenIsoSpec H (f b) (f.map_mem hb) (by decide : 0 < 1)).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map f b)) ≫
        (basicOpenIsoSpec G b hb (by decide : 0 < 1)).inv := by
  apply (cancel_mono (basicOpen G b).ι).mp
  rw [Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι]
  rw [← chart_comp_map f hf (by decide : 0 < 1) b hb]
  simp [awayι]

theorem restriction_finite {b : A} (hb : b ∈ G 1) (hfinite : f.toRingHom.Finite) :
    IsFinite ((ProjRadicalMap.map f hf).resLE (basicOpen G b) (basicOpen H (f b)) le_rfl) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (Away.map f b))) :=
    (IsFinite.SpecMap_iff _).mpr (GradedDehomogenization.away_map_finite G hb f hfinite)
  rw [restriction_eq f hf hb]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem map_finite
    (hcover : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range fun b : G 1 ↦ (b : A)))
    (hfinite : f.toRingHom.Finite) : IsFinite (ProjRadicalMap.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite.{u}) (f := ProjRadicalMap.map f hf)
    (fun b : G 1 ↦ basicOpen G (b : A))
    (Proj.iSup_basicOpen_eq_top G (fun b : G 1 ↦ (b : A)) hcover)]
  intro b
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  change IsFinite ((ProjRadicalMap.map f hf).resLE (basicOpen G (b : A))
    (basicOpen H (f (b : A))) le_rfl)
  exact restriction_finite f hf b.property hfinite

end PaperP1.ProjRadicalCharts
