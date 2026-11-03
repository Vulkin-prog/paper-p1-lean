/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Adapted from Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean,
Mathlib commit 9d581dfff2e41de989072ea63abf3daf69311520.
The admissibility hypothesis is weakened to containment in the radical
of the mapped irrelevant ideal; the dependent constructions use that
proved point map. The upstream dependency is left unchanged.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # A scheme morphism on Proj under the actual radical admissibility criterion -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjRadicalMap

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
  AlgebraicGeometry ProjectiveSpectrum Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

@[simps] def pointComap (p : ProjectiveSpectrum H) : ProjectiveSpectrum G where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le h := by
    apply p.3
    change (HomogeneousIdeal.irrelevant H).toIdeal ≤ p.1.toIdeal
    apply hf.trans
    apply p.2.radical_le_iff.mpr
    exact Ideal.map_le_iff_le_comap.mpr h

def continuousComap : C(ProjectiveSpectrum H, ProjectiveSpectrum G) where
  toFun := pointComap f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf

variable (U : Opens (ProjectiveSpectrum G)) (V : Opens (ProjectiveSpectrum H))
  (hUV : V.1 ⊆ continuousComap f hf ⁻¹' U.1)

def sheafFun (s : ∀ x : U, AtPrime G x.1.1.1) (y : V) : AtPrime H y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl (s ⟨continuousComap f hf y.1, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem locallyFraction (s : ∀ x : U, AtPrime G x.1.1.1) (hs : (isLocallyFraction G).pred s) :
    (isLocallyFraction H).pred (sheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨continuousComap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (continuousComap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [sheafFun]

set_option backward.isDefEq.respectTransparency false in
def sheafMap : (Proj.structureSheaf G).1.obj (.op U) →+* (Proj.structureSheaf H).1.obj (.op V) where
  toFun s := ⟨sheafFun _ _ _ _ hUV s.1, locallyFraction _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [sheafFun]
  map_zero' := by ext; simp [sheafFun]
  map_add' x y := by ext; simp [sheafFun]
  map_mul' x y := by ext; simp [sheafFun]

set_option backward.isDefEq.respectTransparency.types false in
@[simps! (isSimp := false)] def sheafedSpaceMap : Proj.toSheafedSpace H ⟶ Proj.toSheafedSpace G where
  hom :=
    { base := TopCat.ofHom (continuousComap f hf)
      c := { app U := CommRingCat.ofHom (sheafMap f hf _ _ Set.Subset.rfl) } }

theorem germMap {p : ProjectiveSpectrum H}
    (c : NumDenSameDeg G (pointComap f hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace H).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen G _ c)) =
    (toSheafedSpace H).presheaf.germ
      (ProjectiveSpectrum.basicOpen H (f c.den)) p c.4
      (sectionInBasicOpen H p (c.map _ le_rfl)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem localHomStalk (p : ProjectiveSpectrum H) :
    (AlgebraicGeometry.Proj.stalkIso G (pointComap f hf p)).hom ≫ CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
      (AlgebraicGeometry.Proj.stalkIso H p).inv = (sheafedSpaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, AlgebraicGeometry.Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germMap]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
def map : Proj H ⟶ Proj G where
  __ := (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localHomStalk] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hx
    have : IsLocalHom (AlgebraicGeometry.Proj.stalkIso H p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (AlgebraicGeometry.Proj.stalkIso G (pointComap f hf p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A) :
    map f hf ⁻¹ᵁ ProjectiveSpectrum.basicOpen G s = ProjectiveSpectrum.basicOpen H (f s) := rfl

end PaperP1.ProjRadicalMap
