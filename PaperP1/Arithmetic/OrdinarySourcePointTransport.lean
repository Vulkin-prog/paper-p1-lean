module

public import PaperP1.Arithmetic.NormalizedOrdinarySourceEvaluation

/-! # Exact bounded integer-point transport between the ordinary model and actual source curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySourcePointTransport

open MvPolynomial HomogeneousSplitRadicalRelations HomogeneousSplitRadicalVeronese WeightedOrdinaryAffineIdeal
  NormalizedOrdinarySourceEvaluation

variable {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℚ) (D : ℕ) (I J : ι → Finset ℤ)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (H : ℕ) (v : OrdinaryIntegerPoints.Point ι)
  (hv : v ∈ OrdinaryIntegerPoints.curvePoints (ordinaryIdeal c I J) H)

local instance sourcePointDecEq : DecidableEq (SourceProjectiveEmbedding.GeneratorIndex ℚ ι D → ℤ) :=
  Classical.decEq _

include hv in
theorem point_mem_global (hH : 1 ≤ H) :
    OrdinarySourceIntegerLift.point D v ∈ SourceIntegerPoints.curvePoints D
      (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) (H ^ D) := by
  have hdata := (OrdinaryIntegerPoints.mem_curvePoints _ H v).mp hv
  have hbox : v ∈ OrdinaryIntegerPoints.box H := (OrdinaryIntegerPoints.mem_box H v).mpr hdata.1
  apply (SourceIntegerPoints.mem_curvePoints D _ (H ^ D) _).mpr
  refine ⟨(SourceIntegerPoints.mem_box D (H ^ D) _).mp
    (OrdinarySourceIntegerLift.point_mem_box D H hD hH v hbox), ?_⟩
  intro p hp
  have he := RingHom.congr_fun (lift_evaluation_comp c D I J v hdata.1.2 hdata.2 hdeg hD) p
  change SourceIntegerLift.evaluation D (OrdinarySourceIntegerLift.point D v) p =
    sourceEvaluation c D I J v hdata.1.2 hdata.2 (SourceProjectiveEmbedding.evaluation c D I J hdeg hD p) at he
  have hz := RingHom.mem_ker.mp hp
  change SourceProjectiveEmbedding.evaluation c D I J hdeg hD p = 0 at hz
  rw [hz, map_zero] at he
  exact he

include hv in
theorem source_curve_chart_not_mem (P : Ideal (veronese c D I J)) (R : ℕ)
    (hpoint : OrdinarySourceIntegerLift.point D v ∈ SourceIntegerPoints.curvePoints D
      (SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD P) R) :
    OrdinaryCurveSourcePoint.sourceZ c D I J ∉ P := by
  have hdata := (OrdinaryIntegerPoints.mem_curvePoints _ H v).mp hv
  exact source_chart_not_mem c D I J v hdata.1.2 hdata.2 P
    ((containment_iff c D I J v hdata.1.2 hdata.2 hdeg hD P).mpr
      ((SourceIntegerPoints.mem_curvePoints D _ R _).mp hpoint).2)

include hdeg hv in
theorem ordinary_image_point (P : Ideal (veronese c D I J)) (R : ℕ)
    (hpoint : OrdinarySourceIntegerLift.point D v ∈ SourceIntegerPoints.curvePoints D
      (SourceCurveEmbeddingCoordinates.coordinateIdeal c D I J hdeg hD P) R) :
    v ∈ OrdinaryIntegerPoints.curvePoints (SourceCurveOrdinaryImagePrime.ideal c D hD I J P) H := by
  have hdata := (OrdinaryIntegerPoints.mem_curvePoints _ H v).mp hv
  apply (OrdinaryIntegerPoints.mem_curvePoints _ H v).mpr
  refine ⟨hdata.1, ?_⟩
  exact ordinary_image_containment c D I J v hdata.1.2 hdata.2 hD P
    ((containment_iff c D I J v hdata.1.2 hdata.2 hdeg hD P).mpr
      ((SourceIntegerPoints.mem_curvePoints D _ R _).mp hpoint).2)

include hD in
omit [Fintype ι] [DecidableEq ι] in
theorem points_image_card (U : Finset (OrdinaryIntegerPoints.Point ι))
    (hU : ∀ v ∈ U, v (Sum.inl 2) = 1) : (U.image (OrdinarySourceIntegerLift.point D)).card = U.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro v hv w hw he
  exact OrdinarySourceIntegerLift.point_injOn D hD (hU v hv) (hU w hw) he

end PaperP1.OrdinarySourcePointTransport
