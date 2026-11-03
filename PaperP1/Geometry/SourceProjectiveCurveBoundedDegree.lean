module

public import PaperP1.Geometry.SourceProjectiveCurveDegree
public import Mathlib.Tactic.Linarith

/-! # A bounded actual source Hilbert multiplicity bounds its extracted plane equation and actual finite cover rank -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveBoundedDegree

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] [Infinite F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (p : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    ProjectiveSpectrum (SourceVeroneseGrading.sourcePiece c D I J))
  (hheight : (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p).height = 1)

local notation "P₀" => SourceCurveProjectivePointData.ideal s c D I J hdeg hD p

local instance sourceRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P₀) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P₀
local instance baseRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P₀) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P₀

theorem exists_bounded_equation (E : ℕ)
    (hbound : GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P₀)
      (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight) ≤ (D : ℚ) * (E : ℚ)) :
    ∃ (e : ℕ) (f : MvPolynomial (Fin 3) F), 0 < e ∧ f ≠ 0 ∧ f.IsHomogeneous e ∧ Irreducible f ∧
      SourceCurveQuotient.baseIdeal s c D I J hs hD P₀ = PlaneCurveVeroneseBaseQuotient.ideal F f D ∧
      e ≤ E ∧ SourceCurveQuotient.rank s c D I J hs hD P₀ ≤ E := by
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  obtain ⟨e, f, he, hf0, hf, hirr, hbase, hmul⟩ :=
    SourceProjectiveCurveDegree.exists_degree_formula s c D I J hs hdeg hD p hheight
  have hraw := hmul.trans (congrArg (fun r : ℕ ↦ (D : ℚ) * (e : ℚ) * (r : ℚ))
    (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p))
  have hprod : (e : ℚ) * (SourceCurveQuotient.rank s c D I J hs hD P₀ : ℚ) ≤ E := by
    have hDq : 0 < (D : ℚ) := Nat.cast_pos.mpr hD
    rw [hraw] at hbound
    nlinarith
  have hr := (SourceCurveQuotient.rank_bounds s c D I J hs hD P₀ hdeg).1
  have hrQ : (1 : ℚ) ≤ SourceCurveQuotient.rank s c D I J hs hD P₀ := by exact_mod_cast hr
  have heQ : (1 : ℚ) ≤ e := by exact_mod_cast he
  have heE : (e : ℚ) ≤ E := by nlinarith
  have hrE : (SourceCurveQuotient.rank s c D I J hs hD P₀ : ℚ) ≤ E := by nlinarith
  exact ⟨e, f, he, hf0, hf, hirr, hbase, by exact_mod_cast heE, by exact_mod_cast hrE⟩

end PaperP1.SourceProjectiveCurveBoundedDegree
