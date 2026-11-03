module

public import PaperP1.Geometry.OrdinaryRadicalSurface
public import PaperP1.Geometry.OrdinaryCurveSourcePoint
public import PaperP1.Algebra.GradedVeroneseLocalization

/-! # The actual ordinary surface prime and its induced weighted source prime have equal height

The hypothesis concerns the prime in the actual ordinary radical surface,
rather than a separately supplied height condition on its induced source.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveSourceHeight

open MvPolynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.WeightedOrdinaryAffineIdeal PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
  (Q : Ideal (WeightedPolynomial F ι))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)

include hrel in
theorem ordinaryIdeal_le : ordinaryIdeal c I J ≤ Q := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact hrel i

def factor : OrdinaryRing (ordinaryIdeal c I J) →ₐ[F] OrdinaryRing Q :=
  Ideal.Quotient.factorₐ F (ordinaryIdeal_le c I J Q hrel)

def curveMap : OrdinaryVeronese (ordinaryIdeal c I J) D →ₐ[F] OrdinaryRing Q :=
  (factor c I J Q hrel).comp (OrdinaryVeronese (ordinaryIdeal c I J) D).val

def surfaceIdeal : Ideal (OrdinaryVeronese (ordinaryIdeal c I J) D) :=
  RingHom.ker (curveMap c D I J Q hrel).toRingHom

theorem surfaceIdeal_prime [Q.IsPrime] : (surfaceIdeal c D I J Q hrel).IsPrime := RingHom.ker_isPrime _

variable (hD : 0 < D) (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

theorem factor_coordinate (x : HomogeneousSplitRadicalGrading.CoordinateRing c D I J) :
    factor c I J Q hrel
      (coordinateMap c D I J hD hmin hdeg (ordinaryIdeal c I J) (OrdinaryRadicalSurface.relation_mem c I J) x) =
      coordinateMap c D I J hD hmin hdeg Q hrel x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [coordinateMap_mk, coordinateMap_mk]
  rfl

variable (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F))

theorem surfaceIdeal_comap :
    (surfaceIdeal c D I J Q hrel).comap
      (veroneseMap c D I J hD hmin hdeg (ordinaryIdeal c I J)
        (OrdinaryRadicalSurface.relation_mem c I J) (OrdinaryRadicalSurface.homogeneous c I J hmin)).toRingHom =
      sourceIdeal c D I J hD hmin hdeg Q hrel hQ := by
  ext x
  change curveMap c D I J Q hrel
      (veroneseMap c D I J hD hmin hdeg (ordinaryIdeal c I J)
        (OrdinaryRadicalSurface.relation_mem c I J) (OrdinaryRadicalSurface.homogeneous c I J hmin) x) = 0 ↔
    veroneseMap c D I J hD hmin hdeg Q hrel hQ x = 0
  have heq : curveMap c D I J Q hrel
      (veroneseMap c D I J hD hmin hdeg (ordinaryIdeal c I J)
        (OrdinaryRadicalSurface.relation_mem c I J) (OrdinaryRadicalSurface.homogeneous c I J hmin) x) =
      (veroneseMap c D I J hD hmin hdeg Q hrel hQ x : OrdinaryRing Q) :=
    factor_coordinate c D I J Q hrel hD hmin hdeg x.val
  constructor
  · intro h
    exact Subtype.ext (heq.symm.trans h)
  · intro h
    exact heq.trans (congrArg Subtype.val h)

theorem height_eq [Q.IsPrime] (hZ : X (Sum.inl (2 : Fin 3)) ∉ Q) :
    (sourceIdeal c D I J hD hmin hdeg Q hrel hQ).height = (surfaceIdeal c D I J Q hrel).height := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let := OrdinaryRadicalSurface.grading c I J hmin
  let := surfaceIdeal_prime c D I J Q hrel
  let f := gradedCoordinateMap c D I J hD hmin hdeg (ordinaryIdeal c I J) (OrdinaryRadicalSurface.relation_mem c I J)
  have hb : Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3))) ∈
      HomogeneousSplitRadicalGrading.piece c D I J 1 := HomogeneousSplitRadicalGrading.base_variable_mem c D I J 2
  have hne : GradedVeroneseMap.map (HomogeneousSplitRadicalGrading.piece c D I J)
      (ordinaryPiece (ordinaryIdeal c I J)) f
      (coordinateMap c D I J hD hmin hdeg (ordinaryIdeal c I J) (OrdinaryRadicalSurface.relation_mem c I J)).commutes D
      (GradedVeroneseChart.coordinate (HomogeneousSplitRadicalGrading.piece c D I J) D hb) ∉
        surfaceIdeal c D I J Q hrel := by
    intro hm
    have hp : OrdinaryCurveSourcePoint.sourceZ c D I J ∈ sourceIdeal c D I J hD hmin hdeg Q hrel hQ := by
      rw [← surfaceIdeal_comap c D I J Q hrel hD hmin hdeg hQ]
      exact hm
    exact OrdinaryCurveSourcePoint.sourceZ_not_mem c D I J hD hmin hdeg Q hrel hQ hZ hp
  have hh := GradedVeroneseLocalization.height_comap (HomogeneousSplitRadicalGrading.piece c D I J)
    (ordinaryPiece (ordinaryIdeal c I J)) f
    (coordinateMap c D I J hD hmin hdeg (ordinaryIdeal c I J) (OrdinaryRadicalSurface.relation_mem c I J)).commutes
    D hD hb (OrdinaryRadicalSurface.chart_bijective c I J D hD hmin hdeg) (surfaceIdeal c D I J Q hrel) hne
  exact (congrArg Ideal.height (surfaceIdeal_comap c D I J Q hrel hD hmin hdeg hQ)).symm.trans hh

end PaperP1.OrdinaryCurveSourceHeight
