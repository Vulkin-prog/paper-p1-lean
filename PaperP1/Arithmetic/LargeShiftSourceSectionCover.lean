module

public import PaperP1.Arithmetic.SourceNativeIntegerPoint
public import PaperP1.Arithmetic.IntegerBranchShiftHeight
public import PaperP1.Arithmetic.SplitBranchPrimeCertificate
public import PaperP1.Geometry.SourceSurfaceComponentDegreeBudget

/-! # A large original branch shift puts every actual bounded source point on a nonzero radical section -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LargeShiftSourceSectionCover
open PaperP1 Finset Polynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese
  SourceProjectiveEmbedding SourceProjectiveCurveData
local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

variable (s : List (PolynomialRing ℚ)) (d : Fin s.length → ℤ) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (d i : ℚ) (2*D-((I i).card+(J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2*D) (hD : 0 < D)

include hs in
theorem radical_zero (H : ℕ) (hH : 1 ≤ H) (i : Fin s.length) (a : ℤ)
    (ha : a ∈ I i ∨ a ∈ J i) (hlarge : (2 * H ^ 2 : ℕ) < |a|)
    (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : v ∈ SourceIntegerPoints.curvePoints D
      (RingHom.ker (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom) H) :
    SourceIntegerPointEvaluation.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD v
      (SourceIntegerPointEvaluation.valid_of_mem (fun i ↦ (d i : ℚ)) D I J hdeg hD H v hv)
        (HomogeneousSplitRadicalFiniteVeronese.radical (fun i ↦ (d i : ℚ)) D I J i) = 0 := by
  let w := v (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i))
  have hbox := ((SourceIntegerPoints.mem_curvePoints D _ H v).mp hv).1
  let hv' := SourceIntegerPointEvaluation.valid_of_mem (fun i ↦ (d i : ℚ)) D I J hdeg hD H v hv
  have hroot := SourceNativeIntegerPoint.integer_root_equation s D I J hdeg hD d hs v hv' hbox.2 i
  have hw0 : w = 0 := by
    rcases ha with ha | ha
    · apply IntegerBranchShiftHeight.large_shift_forces_zero
        (v (SourceIntegerPoints.affineIndex D hD 1)) w a H hH (hbox.1 _) (hbox.1 _) hlarge
      change v (SourceIntegerPoints.affineIndex D hD 1) + a ∣
        v (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i)) ^ 2
      rw [hroot]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_prod_of_mem _ ha) _) _
    · apply IntegerBranchShiftHeight.large_shift_forces_zero
        (v (SourceIntegerPoints.affineIndex D hD 0)) w a H hH (hbox.1 _) (hbox.1 _) hlarge
      change v (SourceIntegerPoints.affineIndex D hD 0) + a ∣
        v (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i)) ^ 2
      rw [hroot]
      exact dvd_mul_of_dvd_right (dvd_prod_of_mem _ ha) _
  have hh := SourceIntegerPointEvaluation.evaluation_coordinate (fun i ↦ (d i : ℚ)) D I J hdeg hD v hv'
    (SplitWeightedGeneratorIndex.indexEquiv ℚ (Fin s.length) D (Sum.inr i))
  change _ = (w : ℚ) at hh
  exact hh.trans (by rw [hw0, Int.cast_zero])

include hs in
theorem section_cover
    (hd : ∀ i, d i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (H : ℕ) (hH : 1 ≤ H) (a : ℤ) (ha : a ∈ SplitBranchPrimeCertificate.support I J)
    (hlarge : (2 * H ^ 2 : ℕ) < |a|) :
    ∃ curves : Finset (Curve s (fun i ↦ (d i : ℚ)) D I J hdeg hD),
      curves.card ≤ 2 ^ s.length * D ^ 2 ∧
      (∀ Γ ∈ curves, degree s (fun i ↦ (d i : ℚ)) D I J hs hdeg hD Γ ≤
        ((2 ^ s.length * D ^ 2 : ℕ) : ℚ)) ∧
      ∀ v ∈ SourceIntegerPoints.curvePoints D
        (RingHom.ker (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom) H,
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (ideal s (fun i ↦ (d i : ℚ)) D I J hdeg hD Γ) H := by
  classical
  have hi : ∃ i, a ∈ I i ∨ a ∈ J i := by
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      exact ⟨i, Or.inl hi⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
      exact ⟨i, Or.inr hi⟩
  obtain ⟨i, hai⟩ := hi
  obtain ⟨curves, hcard, hdeg', hcover⟩ := SourceSurfaceComponentDegreeBudget.uniform_section_curve_cover
    s (fun i ↦ (d i : ℚ)) D I J hs hdeg hD (fun i ↦ Int.cast_ne_zero.mpr (hd i)) hne hI hJ
    1 (HomogeneousSplitRadicalFiniteVeronese.radical (fun i ↦ (d i : ℚ)) D I J i)
    (SourceVeroneseGrading.source_radical_mem_one _ D I J i)
    (SourceNativeIntegerPoint.radical_ne_zero s (fun i ↦ (d i : ℚ)) D I J hs i)
  refine ⟨curves, by simpa only [one_mul] using hcard, ?_, ?_⟩
  · intro Γ hΓ
    simpa only [one_mul] using (hdeg' Γ hΓ).2
  · intro v hv
    exact hcover H v hv (radical_zero s d D I J hs hdeg hD H hH i a hai hlarge v hv)
end LargeShiftSourceSectionCover
