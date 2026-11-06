module

public import PaperP1.Arithmetic.OrdinarySourceIntegerLift
public import PaperP1.Geometry.SourceCurveOrdinaryImagePrime
public import PaperP1.Geometry.SourceCurveEmbeddingCoordinates
public import PaperP1.Algebra.WeightedOrdinaryAffineIdeal

/-! # Actual ordinary normalized integer solutions evaluate the literal weighted source and its ordinary curve image -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedOrdinarySourceEvaluation

open MvPolynomial HomogeneousSplitRadicalRelations HomogeneousSplitRadicalVeronese WeightedOrdinaryAffineIdeal

variable {ι : Type} (c : ι → ℚ) (D : ℕ) (I J : ι → Finset ℤ) (v : OrdinaryIntegerPoints.Point ι)
  (hZ : v (Sum.inl 2) = 1)
  (hOrd : ordinaryIdeal c I J ≤ RingHom.ker (OrdinaryIntegerPoints.evaluation v).toRingHom)

include hZ hOrd in
theorem weightedIdeal_le_kernel : relationIdeal c D I J ≤ RingHom.ker (OrdinaryIntegerPoints.evaluation v).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (OrdinaryIntegerPoints.evaluation v).toRingHom (relation (c i) D (I i) (J i) i) = 0
  rw [relation_eq_at_one (OrdinaryIntegerPoints.evaluation v).toRingHom (by
    change OrdinaryIntegerPoints.evaluation v (X (Sum.inl (2 : Fin 3))) = 1
    rw [OrdinaryIntegerPoints.evaluation_X, hZ, Int.cast_one])]
  exact hOrd (Ideal.subset_span (Set.mem_range_self i))

def quotientEvaluation : HomogeneousSplitRadicalGrading.CoordinateRing c D I J →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ _ (OrdinaryIntegerPoints.evaluation v) (weightedIdeal_le_kernel c D I J v hZ hOrd)

theorem quotientEvaluation_mk (p : WeightedPolynomial ℚ ι) :
    quotientEvaluation c D I J v hZ hOrd (Ideal.Quotient.mk _ p) = OrdinaryIntegerPoints.evaluation v p := rfl

def sourceEvaluation : veronese c D I J →ₐ[ℚ] ℚ :=
  (quotientEvaluation c D I J v hZ hOrd).comp (veronese c D I J).val

theorem sourceGenerator_value (g : SourceProjectiveEmbedding.GeneratorIndex ℚ ι D) :
    sourceEvaluation c D I J v hZ hOrd (SourceVeroneseGrading.sourceGenerator c D I J g) =
      OrdinaryIntegerPoints.evaluation v (g : WeightedPolynomial ℚ ι) := rfl

theorem lift_evaluation_comp (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) :
    (SourceIntegerLift.evaluation D (OrdinarySourceIntegerLift.point D v)).toRingHom =
      (sourceEvaluation c D I J v hZ hOrd).toRingHom.comp
        (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    have he : (SourceIntegerLift.evaluation D (OrdinarySourceIntegerLift.point D v)).toRingHom.comp C =
        ((sourceEvaluation c D I J v hZ hOrd).toRingHom.comp
          (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom).comp C := Subsingleton.elim _ _
    exact RingHom.congr_fun he a
  · intro g
    change SourceIntegerLift.evaluation D (OrdinarySourceIntegerLift.point D v) (X g) =
      sourceEvaluation c D I J v hZ hOrd (SourceProjectiveEmbedding.evaluation c D I J hdeg hD (X g))
    rw [SourceIntegerLift.evaluation, aeval_X, SourceProjectiveEmbedding.evaluation_X, sourceGenerator_value]
    have he := SourceIntegerLift.evaluation_coordinate D (v (Sum.inl 1)) (v (Sum.inl 0)) (fun i ↦ v (Sum.inr i)) g
    rw [OrdinarySourceIntegerLift.ordinary_reconstruct v hZ] at he
    exact he.symm

theorem sourceZ_value : sourceEvaluation c D I J v hZ hOrd (OrdinaryCurveSourcePoint.sourceZ c D I J) = 1 := by
  change OrdinaryIntegerPoints.evaluation v (X (Sum.inl (2 : Fin 3)) ^ D) = 1
  rw [map_pow, OrdinaryIntegerPoints.evaluation_X, hZ, Int.cast_one, one_pow]

include hZ in
theorem projection_value (p : WeightedPolynomial ℚ ι) :
    OrdinaryIntegerPoints.evaluation v (OrdinaryWeightedProjection.map D p) = OrdinaryIntegerPoints.evaluation v p := by
  have he : (OrdinaryIntegerPoints.evaluation v).comp (OrdinaryWeightedProjection.map D) =
      OrdinaryIntegerPoints.evaluation v := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl j =>
      change OrdinaryIntegerPoints.evaluation v (OrdinaryWeightedProjection.map D (X (Sum.inl j))) = _
      rw [OrdinaryWeightedProjection.map_base, map_mul, map_pow, OrdinaryIntegerPoints.evaluation_X,
        OrdinaryIntegerPoints.evaluation_X, hZ, Int.cast_one, one_pow, mul_one]
    | inr i =>
      change OrdinaryIntegerPoints.evaluation v (OrdinaryWeightedProjection.map D (X (Sum.inr i))) = _
      rw [OrdinaryWeightedProjection.map_radical]
  exact DFunLike.congr_fun he p

theorem source_projection_value (hD : 0 < D) (p : WeightedPolynomial ℚ ι) :
    sourceEvaluation c D I J v hZ hOrd (OrdinarySourcePolynomialProjection.evaluation c D hD I J p) =
      OrdinaryIntegerPoints.evaluation v p := by
  change quotientEvaluation c D I J v hZ hOrd (OrdinarySourcePolynomialProjection.evaluation c D hD I J p).val = _
  rw [OrdinarySourcePolynomialProjection.evaluation_value, quotientEvaluation_mk]
  exact projection_value D v hZ p

theorem containment_iff (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (P : Ideal (veronese c D I J)) :
    P ≤ RingHom.ker (sourceEvaluation c D I J v hZ hOrd).toRingHom ↔
      SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD P ≤
        RingHom.ker (SourceIntegerLift.evaluation D (OrdinarySourceIntegerLift.point D v)).toRingHom := by
  have he := lift_evaluation_comp c D I J v hZ hOrd hdeg hD
  constructor
  · intro h p hp
    exact (RingHom.congr_fun he p).trans (RingHom.mem_ker.mp (h hp))
  · intro h a ha
    obtain ⟨p, hp⟩ := SourceProjectiveEmbedding.evaluation_surjective c D I J hdeg hD a
    have hmem : p ∈ SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD P := by
      change SourceProjectiveEmbedding.evaluation c D I J hdeg hD p ∈ P
      rw [hp]
      exact ha
    have hh := (RingHom.congr_fun he p).symm.trans (RingHom.mem_ker.mp (h hmem))
    change sourceEvaluation c D I J v hZ hOrd (SourceProjectiveEmbedding.evaluation c D I J hdeg hD p) = 0 at hh
    rw [hp] at hh
    exact hh

theorem source_chart_not_mem (P : Ideal (veronese c D I J))
    (hP : P ≤ RingHom.ker (sourceEvaluation c D I J v hZ hOrd).toRingHom) :
    OrdinaryCurveSourcePoint.sourceZ c D I J ∉ P := by
  intro hh
  have he := RingHom.mem_ker.mp (hP hh)
  change sourceEvaluation c D I J v hZ hOrd (OrdinaryCurveSourcePoint.sourceZ c D I J) = 0 at he
  rw [sourceZ_value] at he
  exact one_ne_zero he

theorem ordinary_image_containment (hD : 0 < D) (P : Ideal (veronese c D I J))
    (hP : P ≤ RingHom.ker (sourceEvaluation c D I J v hZ hOrd).toRingHom) :
    SourceCurveOrdinaryImagePrime.ideal c D hD I J P ≤ RingHom.ker (OrdinaryIntegerPoints.evaluation v).toRingHom := by
  intro p hp
  change SourceCurveOrdinaryImagePrime.evaluation c D hD I J P p = 0 at hp
  rw [SourceCurveOrdinaryImagePrime.evaluation_comp, AlgHom.comp_apply] at hp
  have hmem : OrdinarySourcePolynomialProjection.evaluation c D hD I J p ∈ P :=
    Ideal.Quotient.eq_zero_iff_mem.mp hp
  change OrdinaryIntegerPoints.evaluation v p = 0
  rw [← source_projection_value c D I J v hZ hOrd hD p]
  exact RingHom.mem_ker.mp (hP hmem)

end PaperP1.NormalizedOrdinarySourceEvaluation
