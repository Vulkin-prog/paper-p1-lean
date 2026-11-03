/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

The chart compatibility arguments adapt
Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean,
Mathlib commit 9d581dfff2e41de989072ea63abf3daf69311520,
to actual ring maps multiplying homogeneous degrees by D.
-/
module

public import PaperP1.Geometry.ProjDegreeScalingMap
public import PaperP1.Algebra.DegreeScalingAwayMap
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # The actual positive-degree scaling Proj map on homogeneous coordinate charts -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjDegreeScalingCharts

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
  AlgebraicGeometry.ProjectiveSpectrum AlgebraicGeometry.Proj

variable {F A B : Type u} [CommRing F] [CommRing A] [CommRing B] [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B} [GradedAlgebra G] [GradedAlgebra H]
  (D : ℕ) (hD : 0 < D) (f : G →+*ᵍ (fun n ↦ H (n * D)))
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

set_option backward.isDefEq.respectTransparency.types false in
theorem inclusion_comp_map (b : A) :
    (basicOpen H (f b)).ι ≫ ProjDegreeScalingMap.map D hD f hf =
      (ProjDegreeScalingMap.map D hD f hf).resLE _ _ le_rfl ≫ (basicOpen G b).ι := by
  simp only [Scheme.Hom.resLE_comp_ι]
  rfl

theorem awayToSection_comp_appLE {i : ℕ} {b : A} (hb : b ∈ G i) :
    awayToSection G b ≫
      Scheme.Hom.appLE (ProjDegreeScalingMap.map D hD f hf) (basicOpen G b) (basicOpen H (f b)) (by rfl) =
    CommRingCat.ofHom (DegreeScalingAwayMap.map D f b) ≫ awayToSection H (f b) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hb
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    DegreeScalingAwayMap.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp [DegreeScalingHomogeneousMap.fraction]

set_option backward.isDefEq.respectTransparency false in
theorem chart_comp_map {i : ℕ} (hi : 0 < i) (b : A) (hb : b ∈ G i) :
    awayι H (f b) (f.map_mem hb) (Nat.mul_pos hi hD) ≫ ProjDegreeScalingMap.map D hD f hf =
      Spec.map (CommRingCat.ofHom (DegreeScalingAwayMap.map D f b)) ≫ awayι G b hb hi := by
  rw [awayι, awayι, Category.assoc, inclusion_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen H (f b)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE D hD f hf hb]

set_option backward.isDefEq.respectTransparency false in
theorem restriction_eq {i : ℕ} (hi : 0 < i) {b : A} (hb : b ∈ G i) :
    (ProjDegreeScalingMap.map D hD f hf).resLE (basicOpen G b) (basicOpen H (f b)) le_rfl =
      (basicOpenIsoSpec H (f b) (f.map_mem hb) (Nat.mul_pos hi hD)).hom ≫
        Spec.map (CommRingCat.ofHom (DegreeScalingAwayMap.map D f b)) ≫
        (basicOpenIsoSpec G b hb hi).inv := by
  apply (cancel_mono (basicOpen G b).ι).mp
  rw [Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc, basicOpenIsoSpec_inv_ι]
  rw [← chart_comp_map D hD f hf hi b hb]
  simp [awayι]

theorem restriction_isIso {i : ℕ} (hi : 0 < i) {b : A} (hb : b ∈ G i)
    (hbij : Function.Bijective (DegreeScalingAwayMap.map D f b)) :
    IsIso ((ProjDegreeScalingMap.map D hD f hf).resLE (basicOpen G b) (basicOpen H (f b)) le_rfl) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (DegreeScalingAwayMap.map D f b))) :=
    (isIso_SpecMap_iff).mpr hbij
  rw [restriction_eq D hD f hf hi hb]
  infer_instance

end PaperP1.ProjDegreeScalingCharts
