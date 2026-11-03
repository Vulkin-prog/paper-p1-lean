module

public import PaperP1.Geometry.ProjFunctionFieldMap

/-! # Compatibility of the actual scheme function-field map and homogeneous fractions -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjFunctionFieldCompatibility

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace

theorem stalkMap_transport {X Y : Scheme.{u}} (m : X ⟶ Y)
    (p p' : X) (q q' : Y) (hp : p = p') (hq : q = q') (hm : m p = q) (hm' : m p' = q') :
    eqToHom (congrArg (fun y ↦ Y.presheaf.stalk y) hm.symm) ≫ m.stalkMap p ≫
        eqToHom (congrArg (fun x ↦ X.presheaf.stalk x) hp) =
      eqToHom (congrArg (fun y ↦ Y.presheaf.stalk y) hq) ≫
        eqToHom (congrArg (fun y ↦ Y.presheaf.stalk y) hm'.symm) ≫ m.stalkMap p' := by
  subst p'
  subst q'
  simp

variable {A B σ τ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [IsDomain B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain A] [IsDomain B] in
theorem localHomStalk_of_eq (p : ProjectiveSpectrum H) (q : ProjectiveSpectrum G)
    (hq : ProjRadicalMap.map f hf p = q) :
    eqToHom (congrArg (fun y : Proj G ↦ (Proj G).presheaf.stalk y) hq.symm) ≫
        (ProjRadicalMap.map f hf).stalkMap p =
      (AlgebraicGeometry.Proj.stalkIso G q).hom ≫
        CommRingCat.ofHom (localRingHom f q.asHomogeneousIdeal.toIdeal p.asHomogeneousIdeal.toIdeal
          (congrArg (fun q : ProjectiveSpectrum G ↦ q.asHomogeneousIdeal.toIdeal) hq.symm)) ≫
        (AlgebraicGeometry.Proj.stalkIso H p).inv := by
  subst q
  simp only [eqToHom_refl, Category.id_comp]
  change (ProjRadicalMap.sheafedSpaceMap f hf).hom.stalkMap p =
    (AlgebraicGeometry.Proj.stalkIso G (ProjRadicalMap.pointComap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫ (AlgebraicGeometry.Proj.stalkIso H p).inv
  exact (ProjRadicalMap.localHomStalk f hf p).symm

variable (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)

set_option backward.isDefEq.respectTransparency false in
theorem mapCat_comp_catIso :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    ProjFunctionFieldMap.mapCat f hf hG hH hinj ≫ (ProjFunctionField.catIso H hH).hom =
      (ProjFunctionField.catIso G hG).hom ≫ CommRingCat.ofHom (ProjFunctionFieldMap.degreeZeroMap f hinj) := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  have ht := stalkMap_transport (ProjRadicalMap.map f hf)
    (genericPoint (Proj H)) (ProjIntegral.zeroPoint H hH)
    (genericPoint (Proj G)) (ProjIntegral.zeroPoint G hG)
    (ProjIntegral.genericPoint_eq_zero H hH) (ProjIntegral.genericPoint_eq_zero G hG)
    (ProjFunctionFieldMap.genericPoint_map f hf hG hH hinj)
    (ProjFunctionFieldMap.zeroPoint_map f hf hG hH hinj)
  have ht' := congrArg (fun r ↦ r ≫ (AlgebraicGeometry.Proj.stalkIso H (ProjIntegral.zeroPoint H hH)).hom) ht
  rw [localHomStalk_of_eq f hf (ProjIntegral.zeroPoint H hH) (ProjIntegral.zeroPoint G hG)
    (ProjFunctionFieldMap.zeroPoint_map f hf hG hH hinj)] at ht'
  simpa only [ProjFunctionFieldMap.mapCat, ProjFunctionField.catIso, Iso.trans_hom, eqToIso.hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, ProjFunctionFieldMap.degreeZeroMap, ProjIntegral.zeroPoint,
    HomogeneousIdeal.toIdeal_bot] using ht'

set_option backward.isDefEq.respectTransparency false in
theorem equiv_comp_map :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    (ProjFunctionField.equiv H hH).toRingHom.comp (ProjFunctionFieldMap.map f hf hG hH hinj) =
      (ProjFunctionFieldMap.degreeZeroMap f hinj).comp (ProjFunctionField.equiv G hG).toRingHom := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  exact congrArg CommRingCat.Hom.hom (mapCat_comp_catIso f hf hG hH hinj)

end PaperP1.ProjFunctionFieldCompatibility
