module

public import PaperP1.Algebra.PrimitiveRadicalSum
public import PaperP1.Algebra.QuadraticTowerSumBaseChange
public import PaperP1.Algebra.FractionFieldFromGenericGenerator

/-! # The finite radical-sum projection induces the actual isomorphism of fraction fields -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BirationalRadicalProjection

open PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.QuadraticTowerBaseChange PaperP1.QuadraticTowerSumBaseChange

abbrev GenericTower (R K : Type*) [CommRing R] [Field K] [Algebra R K] (s : List R) :=
  Tower K (s.map (algebraMap R K))

def genericMap (R K : Type*) [CommRing R] [Field K] [Algebra R K] (s : List R) :
    Tower R s →+* GenericTower R K s := (mapData (algebraMap R K) s).hom

def imageGenericMap (R K : Type*) [CommRing R] [Field K] [Algebra R K] (s : List R) :
    imageAlgebra R s →+* GenericTower R K s :=
  (genericMap R K s).comp (imageAlgebra R s).val.toRingHom

theorem source_isFractionRing (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    let : Algebra (Tower R s) (GenericTower R K s) := (genericMap R K s).toAlgebra
    IsFractionRing (Tower R s) (GenericTower R K s) := by
  let : Field (GenericTower R K s) := (IndependentQuadraticTower.isField K _ hs).toField
  have hgen : Algebra.adjoin K {genericMap R K s (radicalSum R s)} = ⊤ := by
    change Algebra.adjoin K {(mapData (algebraMap R K) s).hom (radicalSum R s)} = ⊤
    rw [map_radicalSum]
    exact (PrimitiveRadicalSum.independent_sum_primitive K _ hs).1
  exact FractionFieldFromGenericGenerator.isFractionRing (R := R) (K := K) (genericMap R K s)
    (map_injective _ (IsFractionRing.injective R K) s) (mapData (algebraMap R K) s).commutes
    (radicalSum R s) hgen

theorem image_isFractionRing (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    let : Algebra (imageAlgebra R s) (GenericTower R K s) := (imageGenericMap R K s).toAlgebra
    IsFractionRing (imageAlgebra R s) (GenericTower R K s) := by
  let : Field (GenericTower R K s) := (IndependentQuadraticTower.isField K _ hs).toField
  have hinj : Function.Injective (imageGenericMap R K s) :=
    (map_injective _ (IsFractionRing.injective R K) s).comp Subtype.coe_injective
  have hcomm : ∀ r, imageGenericMap R K s (algebraMap R (imageAlgebra R s) r) =
      algebraMap K (GenericTower R K s) (algebraMap R K r) := by
    intro r
    exact (mapData (algebraMap R K) s).commutes r
  let a : imageAlgebra R s := ⟨radicalSum R s, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  have hgen : Algebra.adjoin K {imageGenericMap R K s a} = ⊤ := by
    change Algebra.adjoin K {(mapData (algebraMap R K) s).hom (radicalSum R s)} = ⊤
    rw [map_radicalSum]
    exact (PrimitiveRadicalSum.independent_sum_primitive K _ hs).1
  exact FractionFieldFromGenericGenerator.isFractionRing (R := R) (K := K)
    (imageGenericMap R K s) hinj hcomm a hgen

theorem fractionField_equiv (R K : Type*) [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K] (s : List R)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap R K))) :
    ∃ e : FractionRing (imageAlgebra R s) ≃+* FractionRing (Tower R s),
      ∀ b : imageAlgebra R s,
        e (algebraMap (imageAlgebra R s) (FractionRing (imageAlgebra R s)) b) =
          algebraMap (Tower R s) (FractionRing (Tower R s)) (b : Tower R s) := by
  let : Field (GenericTower R K s) := (IndependentQuadraticTower.isField K _ hs).toField
  have : IsDomain (Tower R s) := source_isDomain (algebraMap R K) (IsFractionRing.injective R K) s inferInstance
  let : Algebra (Tower R s) (GenericTower R K s) := (genericMap R K s).toAlgebra
  let : Algebra (imageAlgebra R s) (GenericTower R K s) := (imageGenericMap R K s).toAlgebra
  have : IsFractionRing (Tower R s) (GenericTower R K s) := source_isFractionRing R K s hs
  have : IsFractionRing (imageAlgebra R s) (GenericTower R K s) := image_isFractionRing R K s hs
  let eA : FractionRing (Tower R s) ≃ₐ[Tower R s] GenericTower R K s := FractionRing.algEquiv (Tower R s) _
  let eB : FractionRing (imageAlgebra R s) ≃ₐ[imageAlgebra R s] GenericTower R K s := FractionRing.algEquiv (imageAlgebra R s) _
  refine ⟨eB.toRingEquiv.trans eA.toRingEquiv.symm, ?_⟩
  intro b
  apply eA.injective
  change eA (eA.symm (eB (algebraMap (imageAlgebra R s) (FractionRing (imageAlgebra R s)) b))) =
    eA (algebraMap (Tower R s) (FractionRing (Tower R s)) (b : Tower R s))
  rw [eA.apply_symm_apply, eB.commutes, eA.commutes]
  rfl

end PaperP1.BirationalRadicalProjection
