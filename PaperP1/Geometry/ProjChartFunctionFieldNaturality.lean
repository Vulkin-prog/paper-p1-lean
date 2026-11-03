module

public import PaperP1.Geometry.ProjChartFunctionField
public import PaperP1.Geometry.ProjRadicalCharts

/-! # The actual chart maps into scheme function fields commute with the projective morphism -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjChartFunctionFieldNaturality

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace

theorem germ_transport {X : Scheme.{u}} (U : X.Opens) (p q : X) (hpq : p = q)
    (hp : p ∈ U) (hq : q ∈ U) :
    X.presheaf.germ U p hp ≫ eqToHom (congrArg (fun x ↦ X.presheaf.stalk x) hpq) =
      X.presheaf.germ U q hq := by
  subst q
  simp

variable {A B σ τ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [IsDomain B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)

set_option backward.isDefEq.respectTransparency false in
theorem germToFunctionField_natural (U : (Proj G).Opens)
    [Nonempty U] [Nonempty (ProjRadicalMap.map f hf ⁻¹ᵁ U)] :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    (Proj G).germToFunctionField U ≫ ProjFunctionFieldMap.mapCat f hf hG hH hinj =
      (ProjRadicalMap.map f hf).app U ≫
        (Proj H).germToFunctionField (ProjRadicalMap.map f hf ⁻¹ᵁ U) := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  have hmap := ProjFunctionFieldMap.genericPoint_map f hf hG hH hinj
  have hmem : genericPoint (Proj G) ∈ U :=
    ((genericPoint_spec (Proj G)).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hpre : ProjRadicalMap.map f hf (genericPoint (Proj H)) ∈ U := hmap.symm ▸ hmem
  change (Proj G).presheaf.germ U (genericPoint (Proj G)) hmem ≫
      (eqToHom (congrArg (fun y : Proj G ↦ (Proj G).presheaf.stalk y) hmap.symm) ≫
        (ProjRadicalMap.map f hf).stalkMap (genericPoint (Proj H))) =
    (ProjRadicalMap.map f hf).app U ≫
      (Proj H).presheaf.germ (ProjRadicalMap.map f hf ⁻¹ᵁ U) (genericPoint (Proj H)) hpre
  rw [← Category.assoc, germ_transport U _ _ hmap.symm hmem hpre]
  exact (ProjRadicalMap.map f hf).germ_stalkMap U (genericPoint (Proj H)) hpre

set_option backward.isDefEq.respectTransparency false in
theorem chartMapCat_natural {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0) (hfb0 : f b ≠ 0) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    ProjChartFunctionField.chartMapCat G hG hb0 ≫ ProjFunctionFieldMap.mapCat f hf hG hH hinj =
      CommRingCat.ofHom (Away.map f b) ≫ ProjChartFunctionField.chartMapCat H hH hfb0 := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  have : Nonempty (Proj.basicOpen G b) := ProjChartFunctionField.nonempty_basicOpen G hG hb0
  have : Nonempty (Proj.basicOpen H (f b)) := ProjChartFunctionField.nonempty_basicOpen H hH hfb0
  have : Nonempty (ProjRadicalMap.map f hf ⁻¹ᵁ Proj.basicOpen G b) := by
    change Nonempty (Proj.basicOpen H (f b))
    infer_instance
  have hg := germToFunctionField_natural f hf hG hH hinj (Proj.basicOpen G b)
  have hs : Proj.awayToSection G b ≫ (ProjRadicalMap.map f hf).app (Proj.basicOpen G b) =
      CommRingCat.ofHom (Away.map f b) ≫ Proj.awayToSection H (f b) :=
    ProjRadicalCharts.awayToSection_comp_appLE f hf hb
  change (Proj.awayToSection G b ≫ (Proj G).germToFunctionField (Proj.basicOpen G b)) ≫
      ProjFunctionFieldMap.mapCat f hf hG hH hinj =
    CommRingCat.ofHom (Away.map f b) ≫
      (Proj.awayToSection H (f b) ≫ (Proj H).germToFunctionField (Proj.basicOpen H (f b)))
  rw [Category.assoc, hg, ← Category.assoc, hs, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem chartMap_natural {b : A} (hb : b ∈ G 1) (hb0 : b ≠ 0) (hfb0 : f b ≠ 0) :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    (ProjFunctionFieldMap.map f hf hG hH hinj).comp (ProjChartFunctionField.chartMap G hG hb0) =
      (ProjChartFunctionField.chartMap H hH hfb0).comp (Away.map f b) := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  exact congrArg CommRingCat.Hom.hom (chartMapCat_natural f hf hG hH hinj hb hb0 hfb0)

end PaperP1.ProjChartFunctionFieldNaturality
