module

public import PaperP1.Geometry.OrdinaryCurveSourceMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-! # An ordinary prime curve meeting Z ≠ 0 constructs its actual source projective point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveSourcePoint

open MvPolynomial PaperP1.HomogeneousSplitRadicalRelations PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F]

local instance weightedRing : CommRing (WeightedPolynomial F ι) := inferInstance

variable (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)

local instance pieceMonoid : SetLike.GradedMonoid (HomogeneousSplitRadicalGrading.piece c D I J) :=
  WeightedPolynomialQuotientGrading.gradedMonoid (weight ι D) (relationIdeal c D I J)

theorem zPower_mem :
    Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3)) ^ D) ∈
      HomogeneousSplitRadicalGrading.piece c D I J D := by
  apply Submodule.mem_map.mpr
  refine ⟨X (Sum.inl (2 : Fin 3)) ^ D, ?_, rfl⟩
  apply (mem_weightedHomogeneousSubmodule F (weight ι D) D _).mpr
  simpa only [smul_eq_mul, mul_one] using (base_variable_homogeneous F ι D 2).pow D

def sourceZ : HomogeneousSplitRadicalVeronese.veronese c D I J := by
  refine ⟨Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3)) ^ D), ?_⟩
  apply GradedVeroneseAlgebra.piece_mem (HomogeneousSplitRadicalGrading.piece c D I J) D 1
  rw [one_mul]
  exact zPower_mem c D I J

theorem sourceZ_mem : sourceZ c D I J ∈ SourceVeroneseGrading.sourcePiece c D I J 1 := by
  change Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3)) ^ D) ∈
    HomogeneousSplitRadicalGrading.piece c D I J (1 * D)
  rw [one_mul]
  exact zPower_mem c D I J

variable (hD : 0 < D) (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (Q : Ideal (WeightedPolynomial F ι))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)
  (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F))
  [Q.IsPrime] (hZ : X (Sum.inl (2 : Fin 3)) ∉ Q)

include hZ in
theorem sourceZ_not_mem : sourceZ c D I J ∉ sourceIdeal c D I J hD hmin hdeg Q hrel hQ := by
  intro hm
  have hz := congrArg (fun z : OrdinaryVeronese Q D ↦ (z : OrdinaryRing Q)) (RingHom.mem_ker.mp hm)
  change (veroneseMap c D I J hD hmin hdeg Q hrel hQ (sourceZ c D I J) : OrdinaryRing Q) = 0 at hz
  rw [veroneseMap_val] at hz
  change coordinateMap c D I J hD hmin hdeg Q hrel
    (Ideal.Quotient.mk _ (X (Sum.inl (2 : Fin 3)) ^ D)) = 0 at hz
  rw [coordinateMap_mk] at hz
  have hpow : (Ideal.Quotient.mk Q (X (Sum.inl (2 : Fin 3))) : OrdinaryRing Q) ^ D = 0 := by
    simpa only [map_pow, WeightedOrdinarySubstitution.map_base] using hz
  exact pow_ne_zero D (fun h ↦ hZ (Ideal.Quotient.eq_zero_iff_mem.mp h)) hpow

def point :
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J) := by
  letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  refine ⟨⟨sourceIdeal c D I J hD hmin hdeg Q hrel hQ,
    sourceIdeal_homogeneous c D I J hD hmin hdeg Q hrel hQ⟩,
    sourceIdeal_prime c D I J hD hmin hdeg Q hrel hQ, ?_⟩
  intro hle
  apply sourceZ_not_mem c D I J hD hmin hdeg Q hrel hQ hZ
  exact hle (HomogeneousIdeal.mem_irrelevant_of_mem (SourceVeroneseGrading.sourcePiece c D I J)
    (by decide : 0 < 1) (sourceZ_mem c D I J))

theorem point_ideal :
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    (point c D I J hD hmin hdeg Q hrel hQ hZ).asHomogeneousIdeal.toIdeal =
      sourceIdeal c D I J hD hmin hdeg Q hrel hQ := rfl

end PaperP1.OrdinaryCurveSourcePoint
