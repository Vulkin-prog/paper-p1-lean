/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Adapted from Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean,
Mathlib commit 9d581dfff2e41de989072ea63abf3daf69311520.
The ring map here multiplies homogeneous degrees by a positive integer D.
The admissibility hypothesis uses the radical of the mapped irrelevant
ideal. Homogeneous localizations use the actual scaled fractions.
The upstream dependency is left unchanged.
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import PaperP1.Algebra.DegreeScalingGrading
public import PaperP1.Algebra.DegreeScalingHomogeneousMap

/-! # A scheme morphism on Proj for an actual positive scaling of homogeneous degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjDegreeScalingMap

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
  AlgebraicGeometry ProjectiveSpectrum Proj

variable {F A B : Type u} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B} [GradedAlgebra G] [GradedAlgebra H]
  (D : ℕ) (hD : 0 < D) (f : G →+*ᵍ (fun n ↦ H (n * D)))
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

@[simps] def pointComap (p : ProjectiveSpectrum H) : ProjectiveSpectrum G where
  asHomogeneousIdeal := DegreeScalingGrading.comap D hD f p.1
  isPrime := p.2.comap f
  not_irrelevant_le h := by
    apply p.3
    change (HomogeneousIdeal.irrelevant H).toIdeal ≤ p.1.toIdeal
    apply hf.trans
    apply p.2.radical_le_iff.mpr
    exact Ideal.map_le_iff_le_comap.mpr h

def continuousComap : C(ProjectiveSpectrum H, ProjectiveSpectrum G) where
  toFun := pointComap D hD f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by
      ext p
      change s ⊆ (DegreeScalingGrading.comap D hD f p.asHomogeneousIdeal : Set A) ↔
        f '' s ⊆ (p.asHomogeneousIdeal : Set B)
      rw [Set.image_subset_iff]
      rfl⟩

open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf

variable (U : Opens (ProjectiveSpectrum G)) (V : Opens (ProjectiveSpectrum H))
  (hUV : V.1 ⊆ continuousComap D hD f hf ⁻¹' U.1)

def sheafFun (s : ∀ x : U, AtPrime G x.1.1.1) (y : V) : AtPrime H y.1.1.1 :=
  DegreeScalingHomogeneousMap.localRingHom D f _ y.1.1.1 rfl (s ⟨continuousComap D hD f hf y.1, hUV y.2⟩)

set_option backward.isDefEq.respectTransparency false in
theorem locallyFraction (s : ∀ x : U, AtPrime G x.1.1.1) (hs : (isLocallyFraction G).pred s) :
    (isLocallyFraction H).pred (sheafFun D hD f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨continuousComap D hD f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (continuousComap D hD f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i * D,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [sheafFun, DegreeScalingHomogeneousMap.val_localRingHom]

set_option backward.isDefEq.respectTransparency false in
def sheafMap : (Proj.structureSheaf G).1.obj (.op U) →+* (Proj.structureSheaf H).1.obj (.op V) where
  toFun s := ⟨sheafFun D hD _ _ _ _ hUV s.1, locallyFraction D hD _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [sheafFun]
  map_zero' := by ext; simp [sheafFun]
  map_add' x y := by ext; simp [sheafFun]
  map_mul' x y := by ext; simp [sheafFun]

set_option backward.isDefEq.respectTransparency.types false in
@[simps! (isSimp := false)] def sheafedSpaceMap : Proj.toSheafedSpace H ⟶ Proj.toSheafedSpace G where
  hom :=
    { base := TopCat.ofHom (continuousComap D hD f hf)
      c := { app U := CommRingCat.ofHom (sheafMap D hD f hf _ _ Set.Subset.rfl) } }

theorem germMap {p : ProjectiveSpectrum H}
    (c : NumDenSameDeg G (pointComap D hD f hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace H).presheaf.germ
      ((Opens.map (sheafedSpaceMap D hD f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap D hD f hf).hom.c.app _ (sectionInBasicOpen G _ c)) =
    (toSheafedSpace H).presheaf.germ
      (ProjectiveSpectrum.basicOpen H (f c.den)) p c.4
      (sectionInBasicOpen H p (DegreeScalingHomogeneousMap.fraction D f (by exact le_rfl) c)) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem localHomStalk (p : ProjectiveSpectrum H) :
    (AlgebraicGeometry.Proj.stalkIso G (pointComap D hD f hf p)).hom ≫ CommRingCat.ofHom (DegreeScalingHomogeneousMap.localRingHom D f _ _ rfl) ≫
      (AlgebraicGeometry.Proj.stalkIso H p).inv = (sheafedSpaceMap D hD f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, AlgebraicGeometry.Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [DegreeScalingHomogeneousMap.val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germMap]
  erw [stalkIso'_germ]
  simp [DegreeScalingHomogeneousMap.fraction]

set_option backward.isDefEq.respectTransparency false in
def map : Proj H ⟶ Proj G where
  __ := (sheafedSpaceMap D hD f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localHomStalk] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hx
    have : IsLocalHom (AlgebraicGeometry.Proj.stalkIso H p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (AlgebraicGeometry.Proj.stalkIso G (pointComap D hD f hf p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A) :
    map D hD f hf ⁻¹ᵁ ProjectiveSpectrum.basicOpen G s = ProjectiveSpectrum.basicOpen H (f s) := rfl

end PaperP1.ProjDegreeScalingMap
