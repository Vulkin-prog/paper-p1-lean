module

public import PaperP1.Geometry.GradedVeroneseProj
public import PaperP1.Geometry.SourceProjectiveRank
public import PaperP1.Algebra.StandardVeroneseCoordinates

/-! # The actual source is a finite flat cover of the standard projective plane -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectivePlane

open AlgebraicGeometry CategoryTheory PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

def plane (F : Type u) [Field F] : Scheme.{u} := Proj (MvPolynomial.homogeneousSubmodule (Fin 3) F)

def baseIso (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    SourceProjectiveMap.baseScheme F D hD ≅ plane F := by
  let := nativeGrading F D hD
  exact (GradedVeroneseProj.iso (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD).symm

theorem baseIso_inv (F : Type u) [Field F] (D : ℕ) (hD : 0 < D) :
    letI := nativeGrading F D hD
    (baseIso F D hD).inv = GradedVeroneseProj.map (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD := rfl

variable {F : Type u} [Field F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

def projection : SourceProjectiveMap.sourceScheme c D I J hdeg hD ⟶ plane F :=
  SourceProjectiveMap.map s c D hD I J hs hdeg ≫ (baseIso F D hD).hom

theorem projection_finite : IsFinite (projection s c D hD I J hs hdeg) := by
  have : IsFinite (SourceProjectiveMap.map s c D hD I J hs hdeg) :=
    SourceProjectiveFinite.map_isFinite s c D hD I J hs hdeg
  dsimp only [projection]
  infer_instance

theorem projection_flat : Flat (projection s c D hD I J hs hdeg) := by
  have : Flat (SourceProjectiveMap.map s c D hD I J hs hdeg) :=
    SourceProjectiveFlat.map_flat s c D hD I J hs hdeg
  dsimp only [projection]
  infer_instance

theorem projection_surjective : Surjective (projection s c D hD I J hs hdeg) := by
  have : Surjective (SourceProjectiveMap.map s c D hD I J hs hdeg) :=
    SourceProjectiveRank.map_surjective s c D hD I J hs hdeg
  dsimp only [projection]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem projection_rank (x : plane F) : (projection s c D hD I J hs hdeg).finrank x = 2 ^ s.length := by
  have : IsFinite (SourceProjectiveMap.map s c D hD I J hs hdeg) :=
    SourceProjectiveFinite.map_isFinite s c D hD I J hs hdeg
  have : Flat (SourceProjectiveMap.map s c D hD I J hs hdeg) :=
    SourceProjectiveFlat.map_flat s c D hD I J hs hdeg
  have : IsFinite (projection s c D hD I J hs hdeg) := projection_finite s c D hD I J hs hdeg
  have : Flat (projection s c D hD I J hs hdeg) := projection_flat s c D hD I J hs hdeg
  have hp : IsPullback (𝟙 _) (SourceProjectiveMap.map s c D hD I J hs hdeg)
      (projection s c D hD I J hs hdeg) (baseIso F D hD).hom :=
    IsPullback.of_horiz_isIso (by simp [projection])
  have hr := Scheme.Hom.finrank_of_isPullback (𝟙 _) (SourceProjectiveMap.map s c D hD I J hs hdeg)
    (projection s c D hD I J hs hdeg) (baseIso F D hD).hom hp ((baseIso F D hD).inv x)
  have hx : (baseIso F D hD).hom ((baseIso F D hD).inv x) = x := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [hx] at hr
  exact hr.symm.trans (SourceProjectiveRank.map_rank s c D hD I J hs hdeg _)

end PaperP1.SourceProjectivePlane
