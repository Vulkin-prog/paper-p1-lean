module

public import PaperP1.Geometry.OrdinaryCurveSourcePoint
public import PaperP1.Algebra.OrdinaryWeightedHomogenization
public import PaperP1.Algebra.WeightedOrdinaryAffineIdeal
public import PaperP1.Algebra.GradedDehomogenizationQuotient
public import PaperP1.Algebra.GradedInjectiveChartMap

/-! # The actual induced source quotient and ordinary quotient have the same Z-chart

The inverse chart map is constructed from the literal inverse homogenization.
No curve dimension, Hilbert polynomial or height hypothesis is used here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveAffineChart

open MvPolynomial HomogeneousLocalization PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F]

local instance weightedRing : CommRing (WeightedPolynomial F ι) := inferInstance

variable (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hD : 0 < D)
  (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (Q : Ideal (WeightedPolynomial F ι))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)
  (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F))

local instance sourceRing : CommRing (SourceRing c D I J hD hmin hdeg Q hrel hQ) := inferInstance
local instance ordinaryRing : CommRing (OrdinaryRing Q) := inferInstance

@[instance_reducible] def sourceGrading : GradedAlgebra (sourcePiece c D I J hD hmin hdeg Q hrel hQ) := by
  letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact HomogeneousQuotientGrading.grading (SourceVeroneseGrading.sourcePiece c D I J)
    (sourceIdeal c D I J hD hmin hdeg Q hrel hQ)
    (sourceIdeal_homogeneous c D I J hD hmin hdeg Q hrel hQ)

@[instance_reducible] def ordinaryGrading : GradedAlgebra (ordinaryPiece Q) :=
  HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q hQ

def sourceZ : SourceRing c D I J hD hmin hdeg Q hrel hQ :=
  Ideal.Quotient.mk _ (OrdinaryCurveSourcePoint.sourceZ c D I J)

theorem sourceZ_mem : sourceZ c D I J hD hmin hdeg Q hrel hQ ∈
    sourcePiece c D I J hD hmin hdeg Q hrel hQ 1 :=
  Submodule.mem_map.mpr ⟨_, OrdinaryCurveSourcePoint.sourceZ_mem c D I J, rfl⟩

def ordinaryZ : OrdinaryRing Q := Ideal.Quotient.mk Q (X (Sum.inl (2 : Fin 3)))

theorem ordinaryZ_mem : ordinaryZ Q ∈ ordinaryPiece Q 1 :=
  Submodule.mem_map.mpr ⟨_, isHomogeneous_X F _, rfl⟩

theorem curveMap_sourceZ : curveMap c D I J hD hmin hdeg Q hrel hQ
    (sourceZ c D I J hD hmin hdeg Q hrel hQ) = ordinaryZ Q ^ D := by
  rw [sourceZ, curveMap_mk]
  change coordinateMap c D I J hD hmin hdeg Q hrel (Ideal.Quotient.mk _
    (X (Sum.inl (2 : Fin 3)) ^ D)) = _
  rw [coordinateMap_mk, map_pow, WeightedOrdinarySubstitution.map_base, map_pow]
  rfl

variable [GradedAlgebra (sourcePiece c D I J hD hmin hdeg Q hrel hQ)] [GradedAlgebra (ordinaryPiece Q)]

def toOrdinaryChart : SourceRing c D I J hD hmin hdeg Q hrel hQ →+*
    Away (ordinaryPiece Q) (ordinaryZ Q) :=
  (GradedDehomogenization.map (ordinaryPiece Q) (ordinaryZ_mem Q)).comp
    (curveMap c D I J hD hmin hdeg Q hrel hQ).toRingHom

omit [GradedAlgebra (sourcePiece c D I J hD hmin hdeg Q hrel hQ)] in
theorem toOrdinaryChart_sourceZ : toOrdinaryChart c D I J hD hmin hdeg Q hrel hQ
    (sourceZ c D I J hD hmin hdeg Q hrel hQ) = 1 := by
  change GradedDehomogenization.map (ordinaryPiece Q) (ordinaryZ_mem Q)
    (curveMap c D I J hD hmin hdeg Q hrel hQ (sourceZ c D I J hD hmin hdeg Q hrel hQ)) = 1
  rw [curveMap_sourceZ, map_pow, GradedDehomogenizationQuotient.map_variable, one_pow]

def quotientMap :
    (SourceRing c D I J hD hmin hdeg Q hrel hQ) ⧸ GradedDehomogenizationQuotient.ideal
      (sourceZ c D I J hD hmin hdeg Q hrel hQ) →+* Away (ordinaryPiece Q) (ordinaryZ Q) :=
  Ideal.Quotient.lift _ (toOrdinaryChart c D I J hD hmin hdeg Q hrel hQ) (by
    change Ideal.span {sourceZ c D I J hD hmin hdeg Q hrel hQ - 1} ≤
      RingHom.ker (toOrdinaryChart c D I J hD hmin hdeg Q hrel hQ)
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    rw [RingHom.map_sub, (toOrdinaryChart c D I J hD hmin hdeg Q hrel hQ).map_one,
      toOrdinaryChart_sourceZ, sub_self])

def map : Away (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
    (sourceZ c D I J hD hmin hdeg Q hrel hQ) →+* Away (ordinaryPiece Q) (ordinaryZ Q) :=
  (quotientMap c D I J hD hmin hdeg Q hrel hQ).comp
    (GradedDehomogenizationQuotient.equiv (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
      (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ)).symm.toRingHom

theorem map_dehomogenization (x : SourceRing c D I J hD hmin hdeg Q hrel hQ) :
    map c D I J hD hmin hdeg Q hrel hQ
      (GradedDehomogenization.map (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
        (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ) x) =
    GradedDehomogenization.map (ordinaryPiece Q) (ordinaryZ_mem Q)
      (curveMap c D I J hD hmin hdeg Q hrel hQ x) := by
  rw [map, RingHom.comp_apply, ← GradedDehomogenizationQuotient.equiv_mk]
  change (quotientMap c D I J hD hmin hdeg Q hrel hQ)
    ((GradedDehomogenizationQuotient.equiv (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
      (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ)).symm
      ((GradedDehomogenizationQuotient.equiv (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
        (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ)) (Ideal.Quotient.mk _ x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

theorem map_mk (n : ℕ) (x : SourceRing c D I J hD hmin hdeg Q hrel hQ)
    (hx : x ∈ sourcePiece c D I J hD hmin hdeg Q hrel hQ (n • (1 : ℕ))) :
    map c D I J hD hmin hdeg Q hrel hQ
      (Away.mk (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
        (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ) n x hx) =
    Away.mk (ordinaryPiece Q) (ordinaryZ_mem Q) (n * D)
      (curveMap c D I J hD hmin hdeg Q hrel hQ x) (by
        simpa only [smul_eq_mul, mul_one] using curveMap_mem c D I J hD hmin hdeg Q hrel hQ n x
          (by simpa only [smul_eq_mul, mul_one] using hx)) := by
  rw [← GradedDehomogenization.map_homogeneous (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
    (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ) n x
    (by simpa only [smul_eq_mul, mul_one] using hx), map_dehomogenization]
  exact GradedDehomogenization.map_homogeneous (ordinaryPiece Q) (ordinaryZ_mem Q) (n * D) _
    (curveMap_mem c D I J hD hmin hdeg Q hrel hQ n x
      (by simpa only [smul_eq_mul, mul_one] using hx))

def inverseGenerator (i : Fin 3 ⊕ ι) : HomogeneousSplitRadicalVeronese.veronese c D I J := by
  letI := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  refine ⟨Ideal.Quotient.mk _ (OrdinaryWeightedHomogenization.generator D i), ?_⟩
  apply GradedVeroneseAlgebra.piece_mem (HomogeneousSplitRadicalGrading.piece c D I J) D 1
  rw [one_mul]
  exact Submodule.mem_map.mpr ⟨_, OrdinaryWeightedHomogenization.generator_homogeneous D hD i, rfl⟩

def inverseMap : WeightedPolynomial F ι →ₐ[F] HomogeneousSplitRadicalVeronese.veronese c D I J :=
  aeval (inverseGenerator c D I J hD hdeg)

theorem inverseMap_val (p : WeightedPolynomial F ι) :
    (inverseMap c D I J hD hdeg p : HomogeneousSplitRadicalGrading.CoordinateRing c D I J) =
      Ideal.Quotient.mk _ (OrdinaryWeightedHomogenization.map D p) := by
  have heq : (HomogeneousSplitRadicalVeronese.veronese c D I J).val.comp (inverseMap c D I J hD hdeg) =
      (Ideal.Quotient.mkₐ F (relationIdeal c D I J)).comp (OrdinaryWeightedHomogenization.map D) := by
    ext i
    simp only [AlgHom.comp_apply, inverseMap, aeval_X, OrdinaryWeightedHomogenization.map]
    rfl
  exact AlgHom.congr_fun heq p

theorem map_surjective : Function.Surjective (map c D I J hD hmin hdeg Q hrel hQ) := by
  intro z
  obtain ⟨a, rfl⟩ := GradedDehomogenization.map_surjective (ordinaryPiece Q) (ordinaryZ_mem Q) z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨GradedDehomogenization.map (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
    (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ)
    (Ideal.Quotient.mk _ (inverseMap c D I J hD hdeg p)), ?_⟩
  rw [map_dehomogenization, curveMap_mk, inverseMap_val, coordinateMap_mk]
  let φ := (GradedDehomogenization.map (ordinaryPiece Q) (ordinaryZ_mem Q)).comp (Ideal.Quotient.mk Q)
  have hZ : φ (X (Sum.inl (2 : Fin 3))) = 1 :=
    GradedDehomogenizationQuotient.map_variable (ordinaryPiece Q) (ordinaryZ_mem Q)
  exact (WeightedOrdinaryAffineIdeal.substitution_eq_at_one φ hZ D _).trans
    (OrdinaryWeightedHomogenization.map_eq_at_one φ hZ D p)

theorem map_injective :
    Function.Injective (map c D I J hD hmin hdeg Q hrel hQ) := by
  apply (injective_iff_map_eq_zero (map c D I J hD hmin hdeg Q hrel hQ)).mpr
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ) z
  rw [map_mk] at hz
  have hzv := congrArg HomogeneousLocalization.val hz
  simp only [Away.val_mk, val_zero] at hzv
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, val_zero]
  exact GradedInjectiveChartMap.localization_zero_of_power
    (curveMap c D I J hD hmin hdeg Q hrel hQ).toRingHom
    (curveMap_injective c D I J hD hmin hdeg Q hrel hQ) D hD
    (sourceZ c D I J hD hmin hdeg Q hrel hQ) (ordinaryZ Q)
    (curveMap_sourceZ c D I J hD hmin hdeg Q hrel hQ) n a hzv

def equiv :
    Away (sourcePiece c D I J hD hmin hdeg Q hrel hQ) (sourceZ c D I J hD hmin hdeg Q hrel hQ) ≃+*
      Away (ordinaryPiece Q) (ordinaryZ Q) :=
  RingEquiv.ofBijective (map c D I J hD hmin hdeg Q hrel hQ)
    ⟨map_injective c D I J hD hmin hdeg Q hrel hQ, map_surjective c D I J hD hmin hdeg Q hrel hQ⟩

omit [GradedAlgebra (sourcePiece c D I J hD hmin hdeg Q hrel hQ)] [GradedAlgebra (ordinaryPiece Q)] in
def actualEquiv :
    letI := sourceGrading c D I J hD hmin hdeg Q hrel hQ
    letI := ordinaryGrading Q hQ
    Away (sourcePiece c D I J hD hmin hdeg Q hrel hQ) (sourceZ c D I J hD hmin hdeg Q hrel hQ) ≃+*
      Away (ordinaryPiece Q) (ordinaryZ Q) := by
  letI := sourceGrading c D I J hD hmin hdeg Q hrel hQ
  letI := ordinaryGrading Q hQ
  exact equiv c D I J hD hmin hdeg Q hrel hQ

omit [GradedAlgebra (sourcePiece c D I J hD hmin hdeg Q hrel hQ)] [GradedAlgebra (ordinaryPiece Q)] in
theorem actualEquiv_dehomogenization (x : SourceRing c D I J hD hmin hdeg Q hrel hQ) :
    letI := sourceGrading c D I J hD hmin hdeg Q hrel hQ
    letI := ordinaryGrading Q hQ
    actualEquiv c D I J hD hmin hdeg Q hrel hQ
      (GradedDehomogenization.map (sourcePiece c D I J hD hmin hdeg Q hrel hQ)
        (sourceZ_mem c D I J hD hmin hdeg Q hrel hQ) x) =
    GradedDehomogenization.map (ordinaryPiece Q) (ordinaryZ_mem Q)
      (curveMap c D I J hD hmin hdeg Q hrel hQ x) := by
  let := sourceGrading c D I J hD hmin hdeg Q hrel hQ
  let := ordinaryGrading Q hQ
  exact map_dehomogenization c D I J hD hmin hdeg Q hrel hQ x

end PaperP1.OrdinaryCurveAffineChart
