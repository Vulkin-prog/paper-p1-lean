module

public import PaperP1.Geometry.SourceCurveProjectiveMap
public import PaperP1.Geometry.ProjFunctionFieldRank
public import Mathlib.Util.TermReduce

/-! # The actual source prime-quotient projection has projective function-field degree equal to its rank -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceCurveProjectiveFieldRank

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.SourceCurveProjectiveMap

local instance polynomialRing (F : Type u) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type u) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type u} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J))
  (b : SourceCurveQuotient.BaseRing s c D I J hs hD P)
  (hb : b ∈ SourceCurveQuotient.basePiece s c D I J hs hD P 1) (hb0 : b ≠ 0)

local instance sourceQuotientRing : CommRing (SourceCurveQuotient.SourceRing s c D I J P) :=
  SourceCurveQuotient.sourceQuotientRing s c D I J P
local instance baseQuotientRing : CommRing (SourceCurveQuotient.BaseRing s c D I J hs hD P) :=
  SourceCurveQuotient.baseQuotientRing s c D I J hs hD P

include hb hb0 in
theorem base_nonempty :
    letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
    (HomogeneousIdeal.irrelevant (SourceCurveQuotient.basePiece s c D I J hs hD P)).toIdeal ≠ ⊥ := by
  let := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  exact ProjIntegral.irrelevant_ne_bot_of_homogeneous _ (by decide : 0 < 1) hb hb0

include hb hb0 in
theorem source_nonempty :
    letI := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
    (HomogeneousIdeal.irrelevant (SourceCurveQuotient.sourcePiece s c D I J P)).toIdeal ≠ ⊥ := by
  let := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  have hfb0 : SourceCurveQuotient.map s c D I J hs hD P b ≠ 0 := fun h ↦ hb0
    (SourceCurveQuotient.map_injective s c D I J hs hD P
      (h.trans (map_zero (SourceCurveQuotient.map s c D I J hs hD P)).symm))
  exact ProjIntegral.irrelevant_ne_bot_of_homogeneous _ (by decide : 0 < 1)
    ((SourceCurveQuotient.map s c D I J hs hD P).map_mem hb) hfb0

include hb hb0 in
theorem baseIntegral [P.IsPrime] :
    IsIntegral (baseScheme s c D I J hs hD P hdeg hP) := by
  let := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  have := SourceCurveQuotient.base_domain s c D I J hs hD P
  exact ProjIntegral.integral _ (base_nonempty s c D I J hs hD P hdeg hP b hb hb0)

include hs hb hb0 in
theorem sourceIntegral [P.IsPrime] :
    IsIntegral (sourceScheme s c D I J hD P hdeg hP) := by
  let := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  have := SourceCurveQuotient.source_domain s c D I J P
  exact ProjIntegral.integral _ (source_nonempty s c D I J hs hD P hdeg hP b hb hb0)

def functionFieldMap [P.IsPrime] :
    letI := baseIntegral s c D I J hs hD P hdeg hP b hb hb0
    letI := sourceIntegral s c D I J hs hD P hdeg hP b hb hb0
    (baseScheme s c D I J hs hD P hdeg hP).functionField →+*
      (sourceScheme s c D I J hD P hdeg hP).functionField := by
  let := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  let := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  have := SourceCurveQuotient.base_domain s c D I J hs hD P
  have := SourceCurveQuotient.source_domain s c D I J P
  let := baseIntegral s c D I J hs hD P hdeg hP b hb hb0
  let := sourceIntegral s c D I J hs hD P hdeg hP b hb hb0
  exact ProjFunctionFieldMap.map (SourceCurveQuotient.map s c D I J hs hD P)
    (admissible s c D I J hs hD P hdeg hP)
    (base_nonempty s c D I J hs hD P hdeg hP b hb hb0)
    (source_nonempty s c D I J hs hD P hdeg hP b hb hb0)
    (SourceCurveQuotient.map_injective s c D I J hs hD P)

/- The specialization preserves the exact field and scalar instances inferred
by the general rank theorem. `beta%` exposes its literal numerical equality
in the public statement, avoiding a costly reconstruction of those instances. -/
set_option linter.defProp false in
abbrev comparisonProof [P.IsPrime] :=
  letI := SourceCurveQuotient.baseGrading s c D I J hs hD P hdeg hP
  letI := SourceCurveQuotient.sourceGrading s c D I J hD P hdeg hP
  letI := SourceCurveQuotient.base_domain s c D I J hs hD P
  letI := SourceCurveQuotient.source_domain s c D I J P
  letI : Algebra (SourceCurveQuotient.BaseRing s c D I J hs hD P) (SourceCurveQuotient.SourceRing s c D I J P) :=
    (SourceCurveQuotient.map s c D I J hs hD P).toRingHom.toAlgebra
  letI : Module (SourceCurveQuotient.BaseRing s c D I J hs hD P) (SourceCurveQuotient.SourceRing s c D I J P) := Algebra.toModule
  let h := ProjFunctionFieldRank.finrank_eq_module
    (F := F) (A := SourceCurveQuotient.BaseRing s c D I J hs hD P)
    (B := SourceCurveQuotient.SourceRing s c D I J P)
    (G := SourceCurveQuotient.basePiece s c D I J hs hD P)
    (H := SourceCurveQuotient.sourcePiece s c D I J P)
    (SourceCurveQuotient.map s c D I J hs hD P)
    (admissible s c D I J hs hD P hdeg hP)
    (base_nonempty s c D I J hs hD P hdeg hP b hb hb0)
    (source_nonempty s c D I J hs hD P hdeg hP b hb hb0)
    (SourceCurveQuotient.map_injective s c D I J hs hD P) hb hb0
    (SourceCurveQuotient.generator s c D I J hs hD P hdeg) (SourceCurveQuotient.weight s c D I J hdeg)
    (SourceCurveQuotient.generator_mem s c D I J hs hD P hdeg)
    (SourceCurveQuotient.generators_span s c D I J hs hD P hdeg)
  h.trans (show Module.finrank (SourceCurveQuotient.BaseRing s c D I J hs hD P)
    (SourceCurveQuotient.SourceRing s c D I J P) = SourceCurveQuotient.rank s c D I J hs hD P from rfl)

theorem finrank [P.IsPrime] : beta%
    (fun {m n : ℕ} (_ : m = n) ↦ m = n) (comparisonProof s c D I J hs hD P hdeg hP b hb hb0) :=
  comparisonProof s c D I J hs hD P hdeg hP b hb hb0

theorem degree_bounds [P.IsPrime] : beta%
    (fun {m n : ℕ} (_ : m = n) ↦ 1 ≤ m ∧ m ≤ 2 ^ s.length)
      (comparisonProof s c D I J hs hD P hdeg hP b hb hb0) :=
  (comparisonProof s c D I J hs hD P hdeg hP b hb hb0).symm ▸
    SourceCurveQuotient.rank_bounds s c D I J hs hD P hdeg

theorem multiplicity [P.IsPrime] (a c₀ : ℚ) (ha : 0 < a)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.basePiece s c D I J hs hD P)
      (Polynomial.C a * Polynomial.X + Polynomial.C c₀))
    (hB : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (SourceCurveQuotient.sourcePiece s c D I J P) p) : beta%
    (fun {m n : ℕ} (_ : m = n) ↦
      GradedHilbertPolynomial.multiplicity (SourceCurveQuotient.sourcePiece s c D I J P) hB = (m : ℚ) * a)
      (comparisonProof s c D I J hs hD P hdeg hP b hb hb0) :=
  (comparisonProof s c D I J hs hD P hdeg hP b hb hb0).symm ▸
    SourceCurveQuotient.multiplicity s c D I J hs hD P hdeg hP a c₀ ha hp hB

end PaperP1.SourceCurveProjectiveFieldRank
