module

public import PaperP1.Geometry.OrdinaryCurveProjectionDegree

/-! # The constructed projective source has Hilbert multiplicity at most D times the actual ordinary curve degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveMultiplicityComparison

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F : Type*} [Field F] [Infinite F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
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

theorem source_multiplicity_le (hheight : (P₀).height = 1) (E : ℕ) (β : ℚ)
    (hOrd : GradedHilbertPolynomial.IsHilbertPolynomial (ordinaryPiece Q) (C (E : ℚ) * X + C β)) :
    GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P₀)
      (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p₀ hheight) ≤ (D : ℚ) * (E : ℚ) := by
  obtain ⟨e, f, _, hf0, hf, _, hbase, hmul⟩ :=
    SourceProjectiveCurveDegree.exists_degree_formula s c D I J hs hdeg hD p₀ hheight
  have hprod := OrdinaryCurveDegreeBound.plane_rank_le_ordinary s c D I J hs hD hmin hdeg Q hrel hQ
    f hf hf0 hbase E β hOrd
  have hraw := hmul.trans (congrArg (fun r : ℕ ↦ (D : ℚ) * (e : ℚ) * (r : ℚ))
    (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p₀))
  have hDq : 0 < (D : ℚ) := Nat.cast_pos.mpr hD
  have hle : (D : ℚ) * (e : ℚ) * (SourceCurveQuotient.rank s c D I J hs hD P₀ : ℚ) ≤
      (D : ℚ) * (E : ℚ) := by nlinarith
  exact hraw.trans_le hle

end PaperP1.OrdinaryCurveMultiplicityComparison
