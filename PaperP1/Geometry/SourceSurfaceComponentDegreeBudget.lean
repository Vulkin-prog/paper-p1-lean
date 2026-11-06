module

public import PaperP1.Geometry.SourceSurfaceSectionCurveDegree
public import PaperP1.Geometry.SourceProjectiveCurveIdealData
public import PaperP1.Algebra.FiniteComponentHilbertBudget

/-! # The actual source section has a uniformly bounded number of literal component curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceComponentDegreeBudget

open Polynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading
  SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
  (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
  (e : ℕ) (f : veronese c D I J) (hf : f ∈ sourcePiece c D I J e) (hf0 : f ≠ 0)

include hs hc hne hI hJ hf hf0

theorem sum_degree_le (curves : Finset (Curve s c D I J hdeg hD))
    (hcurves : ∀ Γ ∈ curves, sourceIdeal s c D I J hdeg hD Γ ∈ (Ideal.span {f}).minimalPrimes) :
    (∑ Γ ∈ curves, degree s c D I J hs hdeg hD Γ) ≤ ((e * (2 ^ s.length * D ^ 2) : ℕ) : ℚ) := by
  classical
  let := sourceGrading c D I J hdeg hD
  let (n : ℕ) : Module.Finite ℚ (sourcePiece c D I J n) :=
    SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  let Q (Γ : curves) := sourceIdeal s c D I J hdeg hD Γ.val
  have hprime (Γ : curves) : (Q Γ).IsPrime :=
    SourceCurveProjectivePointData.ideal_prime s c D I J hdeg hD Γ.val.point
  have hhom (Γ : curves) : (Q Γ).IsHomogeneous (sourcePiece c D I J) :=
    SourceCurveProjectivePointData.ideal_homogeneous s c D I J hdeg hD Γ.val.point
  have hinc (Γ Δ : curves) (hne : Δ ≠ Γ) : ¬ Q Δ ≤ Q Γ := by
    intro hle
    have he : Q Γ = Q Δ := le_antisymm ((hcurves Γ.val Γ.property).2
      ⟨hprime Δ, (hcurves Δ.val Δ.property).le⟩ hle) hle
    apply hne
    apply Subtype.ext
    exact SourceProjectiveCurveIdealData.sourceIdeal_injective s c D I J hdeg hD he.symm
  obtain ⟨b, hb⟩ := SourceSurfaceSectionHilbert.exists_linear_hilbert s c D hD I J hs hdeg hc hne hI hJ e f hf hf0
  have hh := FiniteComponentHilbertBudget.sum_linear_degree_le (sourcePiece c D I J)
    (HomogeneousPrincipalQuotient.ideal f) Q hprime hhom hinc
    (fun Γ ↦ (hcurves Γ.val Γ.property).le) _ b
    (fun Γ ↦ degree s c D I J hs hdeg hD Γ.val)
    (fun Γ ↦ (toCurve s c D I J hs hdeg hD Γ.val).constant) hb
    (fun Γ ↦ SourceProjectiveCurveIdealData.hilbert s c D I J hs hdeg hD Γ.val)
  simpa only [Q, Finset.sum_coe_sort] using hh

theorem curve_count_le (curves : Finset (Curve s c D I J hdeg hD))
    (hcurves : ∀ Γ ∈ curves, sourceIdeal s c D I J hdeg hD Γ ∈ (Ideal.span {f}).minimalPrimes) :
    curves.card ≤ e * (2 ^ s.length * D ^ 2) := by
  have hsum := sum_degree_le s c D I J hs hdeg hD hc hne hI hJ e f hf hf0 curves hcurves
  have hcount : (curves.card : ℚ) ≤ ∑ Γ ∈ curves, degree s c D I J hs hdeg hD Γ := by
    calc
      (curves.card : ℚ) = ∑ _Γ ∈ curves, (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun Γ _hΓ ↦
        SourceProjectiveCurveIdealData.one_le_degree s c D I J hs hdeg hD Γ)
  exact_mod_cast hcount.trans hsum

theorem uniform_section_curve_cover :
    ∃ curves : Finset (Curve s c D I J hdeg hD),
      curves.card ≤ e * (2 ^ s.length * D ^ 2) ∧
      (∀ Γ ∈ curves, f ∈ sourceIdeal s c D I J hdeg hD Γ ∧
        degree s c D I J hs hdeg hD Γ ≤ ((e * (2 ^ s.length * D ^ 2) : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ)
        (hv : v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H),
        SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v
          (SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv) f = 0 →
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (ideal s c D I J hdeg hD Γ) H := by
  obtain ⟨curves, hcurves, hcover⟩ := SourcePrincipalComponentCurves.finite_curve_cover s c D I J hdeg hD
    hs hc hne hI hJ e f hf hf0
  refine ⟨curves, curve_count_le s c D I J hs hdeg hD hc hne hI hJ e f hf hf0 curves
    (fun Γ hΓ ↦ (hcurves Γ hΓ).2), ?_, hcover⟩
  intro Γ hΓ
  exact ⟨(hcurves Γ hΓ).1, SourceSurfaceSectionCurveDegree.degree_le s c D I J hs hdeg hD hc hne hI hJ
    e f hf hf0 Γ (hcurves Γ hΓ).1⟩

end PaperP1.SourceSurfaceComponentDegreeBudget
