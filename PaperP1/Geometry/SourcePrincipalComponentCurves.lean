module

public import PaperP1.Algebra.HomogeneousPrincipalComponents
public import PaperP1.Geometry.SourceProjectiveCurveData
public import PaperP1.Arithmetic.SourceIntegerPointEvaluation
public import Mathlib.RingTheory.FiniteType

/-! # Actual homogeneous divisor components construct the companion's literal source-projective curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourcePrincipalComponentCurves

open MvPolynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading
  SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)

def chartCoordinate : veronese c D I J := sourceGenerator c D I J (SourceIntegerPoints.normalizer D)

variable (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)

def toCurve (P : Ideal (veronese c D I J)) (hprime : P.IsPrime)
    (hhom : letI := sourceGrading c D I J hdeg hD; P.IsHomogeneous (sourcePiece c D I J))
    (hheight : P.height = 1) (hz : chartCoordinate s c D I J ∉ P) : Curve s c D I J hdeg hD := by
  let := sourceGrading c D I J hdeg hD
  let p : ProjectiveSpectrum (sourcePiece c D I J) := {
    asHomogeneousIdeal := ⟨P, hhom⟩
    isPrime := hprime
    not_irrelevant_le := by
      intro hle
      apply hz
      exact hle (HomogeneousIdeal.mem_irrelevant_of_mem (sourcePiece c D I J) (by decide : 0 < 1)
        (sourceGenerator_mem_one c D I J (SourceIntegerPoints.normalizer D))) }
  exact { point := p, height := hheight }

theorem toCurve_sourceIdeal (P : Ideal (veronese c D I J)) (hprime : P.IsPrime)
    (hhom : letI := sourceGrading c D I J hdeg hD; P.IsHomogeneous (sourcePiece c D I J))
    (hheight : P.height = 1) (hz : chartCoordinate s c D I J ∉ P) :
    sourceIdeal s c D I J hdeg hD (toCurve s c D I J hdeg hD P hprime hhom hheight hz) = P := rfl

theorem point_membership (Γ : Curve s c D I J hdeg hD) (H : ℕ)
    (v : SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : v ∈ SourceIntegerPoints.curvePoints D
      (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H)
    (hΓ : sourceIdeal s c D I J hdeg hD Γ ≤ RingHom.ker
      (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
        (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv)).toRingHom) :
    v ∈ SourceIntegerPoints.curvePoints D (ideal s c D I J hdeg hD Γ) H := by
  have hbox := (SourceIntegerPoints.mem_curvePoints _ _ _ _).mp hv |>.1
  apply (SourceIntegerPoints.mem_curvePoints _ _ _ _).mpr
  refine ⟨hbox, ?_⟩
  intro P hP
  have hmem : aeval (R := ℚ) (sourceGenerator c D I J) P ∈ sourceIdeal s c D I J hdeg hD Γ := hP
  have hh := hΓ hmem
  change SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
    (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv)
      (aeval (R := ℚ) (sourceGenerator c D I J) P) = 0 at hh
  rw [SourceIntegerPointEvaluation.evaluation_polynomial] at hh
  exact hh

theorem finite_curve_cover
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (e : ℕ) (f : veronese c D I J) (hf : f ∈ sourcePiece c D I J e) (hf0 : f ≠ 0) :
    ∃ curves : Finset (Curve s c D I J hdeg hD),
      (∀ Γ ∈ curves, f ∈ sourceIdeal s c D I J hdeg hD Γ) ∧
      ∀ (H : ℕ) (v : SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ)
        (hv : v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H),
        SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
          (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv) f = 0 →
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (ideal s c D I J hdeg hD Γ) H := by
  classical
  let A := veronese c D I J
  let := sourceGrading c D I J hdeg hD
  let := source_isDomain s c D I J hs hc hne hI hJ
  let : Algebra.FiniteType ℚ A := HomogeneousSplitRadicalVeronese.finiteType c D hD I J
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℚ A
  have hcomponents := HomogeneousPrincipalComponents.finite_cover (sourcePiece c D I J) hf hf0
  let T := (HomogeneousPrincipalComponents.components f).filter (fun P ↦ chartCoordinate s c D I J ∉ P)
  let make (P : T) : Curve s c D I J hdeg hD :=
    toCurve s c D I J hdeg hD P.val
      (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).1
      (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).2.1
      (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).2.2.1
      (Finset.mem_filter.mp P.property).2
  let curves := T.attach.image make
  refine ⟨curves, ?_, ?_⟩
  · intro Γ hΓ
    obtain ⟨P, _hP, rfl⟩ := Finset.mem_image.mp hΓ
    change f ∈ P.val
    exact (hcomponents.1 P.val (Finset.mem_filter.mp P.property).1).2.2.2
  · intro H v hv hzero
    let φ := SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
      (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv)
    have hφb : φ (chartCoordinate s c D I J) = 1 := by
      change SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v _
        (sourceGenerator c D I J (SourceIntegerPoints.normalizer D)) = 1
      rw [SourceIntegerPointEvaluation.evaluation_coordinate,
        (SourceIntegerPoints.mem_curvePoints _ _ _ _).mp hv |>.1.2, Int.cast_one]
    obtain ⟨P, hP, hPQ, hb⟩ := hcomponents.2 φ (chartCoordinate s c D I J) hzero (by rw [hφb]; exact one_ne_zero)
    have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hP, hb⟩
    let P' : T := ⟨P, hPT⟩
    refine ⟨make P', Finset.mem_image.mpr ⟨P', Finset.mem_attach _ _, rfl⟩, ?_⟩
    apply point_membership s c D I J hdeg hD (make P') H v hv
    change P ≤ RingHom.ker φ.toRingHom
    exact hPQ

end PaperP1.SourcePrincipalComponentCurves
