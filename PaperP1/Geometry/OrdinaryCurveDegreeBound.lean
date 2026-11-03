module

public import PaperP1.Geometry.OrdinaryCurveSourceMap
public import PaperP1.Algebra.SourceCurvePlaneEquationHilbert
public import PaperP1.Algebra.LinearHilbertSlopeComparison

/-! # Actual ordinary curve Hilbert growth bounds the extracted plane degree times the actual cover rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveDegreeBound

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

local notation "P₀" => sourceIdeal c D I J hD hmin hdeg Q hrel hQ

local instance sourceRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P₀) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P₀
local instance baseRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P₀) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P₀

include hs in
theorem plane_rank_le_ordinary {e : ℕ} (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous e)
    (hf0 : f ≠ 0)
    (hbase : SourceCurveQuotient.baseIdeal s c D I J hs hD P₀ = PlaneCurveVeroneseBaseQuotient.ideal F f D)
    (δ β : ℚ)
    (hOrd : GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q) (C δ * X + C β)) :
    (e : ℚ) * (SourceCurveQuotient.rank s c D I J hs hD P₀ : ℚ) ≤ δ := by
  let : (P₀).IsPrime := sourceIdeal_prime c D I J hD hmin hdeg Q hrel hQ
  let (n : ℕ) : Module.Finite F (ordinaryPiece Q n) := ordinaryPiece_finite Q n
  have hP := sourceIdeal_homogeneous c D I J hD hmin hdeg Q hrel hQ
  have hbaseHP := SourceCurvePlaneEquationHilbert.base_isHilbertPolynomial s c D I J hs hD P₀ f hf hf0 hbase
  have hsource := SourceCurveQuotient.hasSlope s c D I J hs hD P₀ hdeg hP
    ((D : ℚ) * (e : ℚ)) ((3 * (e : ℚ) - (e : ℚ) ^ 2) / 2) hbaseHP
  have hbound := LinearHilbertSlopeComparison.slope_le_of_injective
    (sourcePiece c D I J hD hmin hdeg Q hrel hQ) (ordinaryPiece Q)
    ((SourceCurveQuotient.rank s c D I J hs hD P₀ : ℚ) * ((D : ℚ) * (e : ℚ))) δ
    hsource (LinearHilbertGrowth.of_affine_polynomial hOrd) D hD
    (curveMap c D I J hD hmin hdeg Q hrel hQ).toLinearMap
    (curveMap_injective c D I J hD hmin hdeg Q hrel hQ)
    (curveMap_mem c D I J hD hmin hdeg Q hrel hQ)
  have hDq : 0 < (D : ℚ) := Nat.cast_pos.mpr hD
  nlinarith

include hs in
theorem degree_bounds {e : ℕ} (f : MvPolynomial (Fin 3) F) (he : 0 < e)
    (hf : f.IsHomogeneous e) (hf0 : f ≠ 0)
    (hbase : SourceCurveQuotient.baseIdeal s c D I J hs hD P₀ = PlaneCurveVeroneseBaseQuotient.ideal F f D)
    (E : ℕ) (β : ℚ)
    (hOrd : GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q) (C (E : ℚ) * X + C β)) :
    e ≤ E ∧ SourceCurveQuotient.rank s c D I J hs hD P₀ ≤ E := by
  have hbound := plane_rank_le_ordinary s c D I J hs hD hmin hdeg Q hrel hQ f hf hf0 hbase E β hOrd
  let : (P₀).IsPrime := sourceIdeal_prime c D I J hD hmin hdeg Q hrel hQ
  have hr := (SourceCurveQuotient.rank_bounds s c D I J hs hD P₀ hdeg).1
  have hrQ : (1 : ℚ) ≤ SourceCurveQuotient.rank s c D I J hs hD P₀ := by exact_mod_cast hr
  have heQ : (1 : ℚ) ≤ e := by exact_mod_cast he
  constructor
  · have h : (e : ℚ) ≤ E := by nlinarith
    exact_mod_cast h
  · have h : (SourceCurveQuotient.rank s c D I J hs hD P₀ : ℚ) ≤ E := by nlinarith
    exact_mod_cast h

end PaperP1.OrdinaryCurveDegreeBound
