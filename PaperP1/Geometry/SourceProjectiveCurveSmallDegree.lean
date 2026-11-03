module

public import PaperP1.Geometry.SourceProjectiveCurveDegree
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.Field.Rat
public import Lean.Elab.Tactic.Omega

/-! # An actual source curve below degree 2D has a linear plane image and field degree one -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveCurveSmallDegree

theorem factors_lt_two {D e r : ℕ} (hD : 0 < D) (he : 0 < e) (hr : 0 < r)
    (h : (D : ℚ) * (e : ℚ) * (r : ℚ) < 2 * (D : ℚ)) : e = 1 ∧ r = 1 := by
  have hDQ : 0 < (D : ℚ) := Nat.cast_pos.mpr hD
  have hpQ : (e : ℚ) * (r : ℚ) < 2 := (mul_lt_mul_iff_right₀ hDQ).mp (by nlinarith [h])
  have hp : e * r < 2 := by exact_mod_cast hpQ
  have he_le := Nat.le_mul_of_pos_right e hr
  have hr_le := Nat.le_mul_of_pos_left r he
  omega

open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData

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

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD
    (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p)

theorem line_and_degree_one
    (hsmall : GradedHilbertPolynomial.multiplicity
      (SourceCurveQuotient.sourcePiece s c D I J (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p))
      (SourceProjectiveCurveDegree.exists_polynomial s c D I J hs hdeg hD p hheight) < 2 * (D : ℚ)) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      ∃ f : MvPolynomial (Fin 3) F, f ≠ 0 ∧ f.IsHomogeneous 1 ∧ Irreducible f ∧
        SourceCurveQuotient.baseIdeal s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) =
          PlaneCurveVeroneseBaseQuotient.ideal F f D ∧ m = 1)
      (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p) := by
  let := SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD p
  obtain ⟨e, f, he, hf0, hf, hirr, hbase, hmul⟩ :=
    SourceProjectiveCurveDegree.exists_degree_formula s c D I J hs hdeg hD p hheight
  have hb := (SourceProjectiveCurveDegree.comparisonProof s c D I J hs hdeg hD p).symm ▸
    SourceCurveQuotient.rank_bounds s c D I J hs hD (SourceCurveProjectivePointData.ideal s c D I J hdeg hD p) hdeg
  have hprod := hmul ▸ hsmall
  obtain ⟨he1, hr1⟩ := factors_lt_two hD he hb.1 hprod
  exact ⟨f, hf0, by simpa only [he1] using hf, hirr, hbase, hr1⟩

end PaperP1.SourceProjectiveCurveSmallDegree
