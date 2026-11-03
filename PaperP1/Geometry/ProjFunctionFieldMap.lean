module

public import PaperP1.Geometry.ProjFunctionField
public import PaperP1.Geometry.ProjRadicalMap

/-! # The actual projective morphism induces the map at generic-point function fields -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.ProjFunctionFieldMap

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace

variable {A B σ τ : Type u} [CommRing A] [IsDomain A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [IsDomain B] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H)
  (hf : (HomogeneousIdeal.irrelevant H).toIdeal ≤
    ((HomogeneousIdeal.irrelevant G).toIdeal.map f.toRingHom).radical)
  (hG : (HomogeneousIdeal.irrelevant G).toIdeal ≠ ⊥)
  (hH : (HomogeneousIdeal.irrelevant H).toIdeal ≠ ⊥) (hinj : Function.Injective f)

include hinj in
theorem zeroPoint_map :
    ProjRadicalMap.map f hf (ProjIntegral.zeroPoint H hH) = ProjIntegral.zeroPoint G hG := by
  change ProjRadicalMap.pointComap f hf (ProjIntegral.zeroPoint H hH) = ProjIntegral.zeroPoint G hG
  ext a
  change f a = 0 ↔ a = 0
  exact ⟨fun h ↦ hinj (h.trans (map_zero f).symm), fun h ↦ h ▸ map_zero f⟩

include hinj in
theorem genericPoint_map :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    ProjRadicalMap.map f hf (genericPoint (Proj H)) = genericPoint (Proj G) := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  rw [ProjIntegral.genericPoint_eq_zero G hG, ProjIntegral.genericPoint_eq_zero H hH]
  exact zeroPoint_map f hf hG hH hinj

def map :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    (Proj G).functionField →+* (Proj H).functionField := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  let e := congrArg (fun p : Proj G ↦ (Proj G).presheaf.stalk p)
    (genericPoint_map f hf hG hH hinj).symm
  exact (eqToHom e ≫ (ProjRadicalMap.map f hf).stalkMap (genericPoint (Proj H))).hom

theorem map_injective :
    letI := ProjIntegral.integral G hG
    letI := ProjIntegral.integral H hH
    Function.Injective (map f hf hG hH hinj) := by
  let := ProjIntegral.integral G hG
  let := ProjIntegral.integral H hH
  exact (map f hf hG hH hinj).injective

def degreeZeroMap : ProjFunctionField.degreeZeroField G →+* ProjFunctionField.degreeZeroField H :=
  localRingHom f (⊥ : Ideal A) (⊥ : Ideal B) (by
    ext a
    change a = 0 ↔ f a = 0
    exact ⟨fun h ↦ h ▸ map_zero f, fun h ↦ hinj (h.trans (map_zero f).symm)⟩)

end PaperP1.ProjFunctionFieldMap
