/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Adapted from Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean,
Mathlib commit 9d581dfff2e41de989072ea63abf3daf69311520.
The chart naturality proof is applied to the internally checked radical-admissible
projective morphism. Upstream sources and compiler options are unchanged.
-/
module

public import PaperP1.Geometry.ProjRadicalMap

/-! # Exact affine-chart naturality for the checked radical-admissible projective map -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjRadicalMapCharts

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
  AlgebraicGeometry AlgebraicGeometry.Proj
open PaperP1.ProjRadicalMap

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

theorem inclusion_comp (s : A) : (basicOpen H (f s)).ι ≫ ProjRadicalMap.map f hf =
    (ProjRadicalMap.map f hf).resLE (basicOpen G s) (basicOpen H (f s))
      (by intro p hp; exact hp) ≫ (basicOpen G s).ι := by
  exact (Scheme.Hom.resLE_comp_ι _ _).symm

theorem section_comp {i : ℕ} {s : A} (hs : s ∈ G i) :
    awayToSection G s ≫
      Scheme.Hom.appLE (ProjRadicalMap.map f hf) (basicOpen G s) (basicOpen H (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away G s →+* Away H (f s)) ≫
      awayToSection H (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

theorem chart_comp {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ G i) :
    awayι H (f s) (f.map_mem hs) hi ≫ ProjRadicalMap.map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι G s hs hi := by
  rw [awayι, awayι, Category.assoc, inclusion_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen H (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top]
  convert! section_comp f hf hs using 1

end PaperP1.ProjRadicalMapCharts
