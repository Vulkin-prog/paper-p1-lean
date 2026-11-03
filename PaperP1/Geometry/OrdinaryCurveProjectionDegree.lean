module

public import PaperP1.Geometry.OrdinaryCurveDegreeBound
public import PaperP1.Geometry.OrdinaryCurveSourcePoint
public import PaperP1.Geometry.SourceProjectiveCurveDegree

/-! # An ordinary curve constructs its source point and bounds its extracted image and actual projective field degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveProjectionDegree

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hD : 0 < D) (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (Q : Ideal (WeightedPolynomial F (Fin s.length)))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)
  (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3 ⊕ Fin s.length) F)) [Q.IsPrime]
  (hZ : MvPolynomial.X (Sum.inl (2 : Fin 3)) ∉ Q)

local notation "P₀" => sourceIdeal c D I J hD hmin hdeg Q hrel hQ
local notation "p₀" => OrdinaryCurveSourcePoint.point c D I J hD hmin hdeg Q hrel hQ hZ

local instance sourceRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P₀) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P₀
local instance baseRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P₀) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P₀

include hZ in
theorem exists_plane_equation (hheight : (P₀).height = 1) :
    ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
      SourceCurveQuotient.baseIdeal s c D I J hs hD P₀ = PlaneCurveVeroneseBaseQuotient.ideal F f D := by
  let : (P₀).IsPrime := sourceIdeal_prime c D I J hD hmin hdeg Q hrel hQ
  have hP := sourceIdeal_homogeneous c D I J hD hmin hdeg Q hrel hQ
  let b : SourceCurveQuotient.BaseRing s c D I J hs hD P₀ :=
    SourceCurveProjectivePointData.coordinate s c D I J hs hdeg hD p₀
  have hb : b ∈ SourceCurveQuotient.basePiece s c D I J hs hD P₀ 1 :=
    SourceCurveProjectivePointData.coordinate_mem s c D I J hs hdeg hD p₀
  have hb0 : b ≠ 0 := SourceCurveProjectivePointData.coordinate_ne_zero s c D I J hs hdeg hD p₀
  exact SourceCurvePlaneImageEquation.exists_equation s c D I J hs hD P₀ hdeg hP b hb hb0
    (SourceCurveProjectionHeight.plane_height_one s c D I J hs hD P₀ hdeg hP b hb hb0 hheight)

include hZ in
theorem exists_rank_bounds (hheight : (P₀).height = 1) (E : ℕ) (β : ℚ)
    (hOrd : GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q) (C (E : ℚ) * X + C β)) :
    ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
      SourceCurveQuotient.baseIdeal s c D I J hs hD P₀ = PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
      e ≤ E ∧ SourceCurveQuotient.rank s c D I J hs hD P₀ ≤ E := by
  obtain ⟨e, f, he, hf0, hf, hirr, hbase⟩ := exists_plane_equation s c D I J hs hD hmin hdeg Q hrel hQ hZ hheight
  obtain ⟨heE, hrE⟩ := OrdinaryCurveDegreeBound.degree_bounds s c D I J hs hD hmin hdeg Q hrel hQ
    f he hf hf0 hbase E β hOrd
  exact ⟨e, f, he, hf0, hf, hirr, hbase, heE, hrE⟩

include hZ in
theorem exists_degree_bounds [Infinite F] (hheight : (P₀).height = 1) (E : ℕ) (β : ℚ)
    (hOrd : GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q) (C (E : ℚ) * X + C β)) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
        SourceCurveQuotient.baseIdeal s c D I J hs hD P₀ = PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
        e ≤ E ∧ m ≤ E)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p₀) := by
  obtain ⟨e, f, he, hf0, hf, hirr, hbase, heE, hrE⟩ :=
    exists_rank_bounds s c D I J hs hD hmin hdeg Q hrel hQ hZ hheight E β hOrd
  refine ⟨e, f, he, hf0, hf, hirr, hbase, heE, ?_⟩
  exact (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p₀).symm ▸ hrE

end PaperP1.OrdinaryCurveProjectionDegree
