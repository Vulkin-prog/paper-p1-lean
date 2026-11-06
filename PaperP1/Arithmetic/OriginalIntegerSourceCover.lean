module

public import PaperP1.Arithmetic.IntegerExactSourceSurfaceCover
public import PaperP1.Arithmetic.OriginalSourceProjectedCover
public import PaperP1.Arithmetic.LargeShiftSourceSectionCover
public import PaperP1.Arithmetic.SourceSurfaceCoverUnderP3

/-! # Unconditional genuine-degree covers of every actual integer source, uniform before all coefficients, shifts and heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalIntegerSourceCover
open PaperP1 MvPolynomial Finset HomogeneousSplitRadicalData SourceProjectiveEmbedding SourceVeroneseGrading
  SourceSurfaceBoundedProjection SourceIntegerHypersurfaceProjection SourceProjectiveCurveData
local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _
attribute [local instance] MvPolynomial.gradedAlgebra

theorem support_card_bound {ι : Type*} [Fintype ι] (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    (SplitBranchPrimeCertificate.support I J).card ≤ Fintype.card ι * (2 * D) := by
  classical
  calc
    _ ≤ (univ.biUnion I).card + (univ.biUnion J).card := card_union_le _ _
    _ ≤ (∑ i, (I i).card) + ∑ i, (J i).card :=
      Nat.add_le_add (card_biUnion_le) (card_biUnion_le)
    _ = ∑ i, ((I i).card + (J i).card) := (sum_add_distrib).symm
    _ ≤ ∑ _i : ι, 2 * D := sum_le_sum (fun i _ ↦ hdeg i)
    _ = _ := by simp

theorem bounded_shifts_cover (k D : ℕ) (hD : 0 < D) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧
      ∀ (s : List (PolynomialRing ℚ)), s.length = k →
      ∀ (cZ : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ)
        (hs : ∀ i, s.get i = radicand (cZ i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
        (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D),
        (∀ i, cZ i ≠ 0) → (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
        (Pairwise fun i j ↦ Disjoint (I i) (I j)) → (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      ∀ H : ℕ, 1 ≤ H →
      (∀ b ∈ SplitBranchPrimeCertificate.support I J, |b| ≤ (2 * H ^ 2 : ℕ)) → ∀ U : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ),
        U ⊆ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation (fun i ↦ (cZ i : ℚ)) D I J hdeg hD).toRingHom) H →
        ∃ (V : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ))
            (curves : Finset (Curve s (fun i ↦ (cZ i : ℚ)) D I J hdeg hD)),
          V ⊆ U ∧ (∀ Γ ∈ curves, degree s (fun i ↦ (cZ i : ℚ)) D I J hs hdeg hD Γ ≤ (B : ℚ)) ∧
          (V.card : ℝ) ≤ C * (H : ℝ) ^ (2 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) ∧
          (curves.card : ℝ) ≤ C * (H : ℝ) ^ (1 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) ∧
          ∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves,
            v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s (fun i ↦ (cZ i : ℚ)) D I J hdeg hD Γ) H := by
  classical
  obtain ⟨M, A, hA, hP3⟩ := OriginalSourceProjectedCover.uniform_cover k D (k * (2 * D)) hD δ hδ
  let d := 2 ^ k * D ^ 2
  let L := heightFactor k D
  let p := 1 / Real.sqrt (d : ℝ) + δ
  let q := 2 / Real.sqrt (d : ℝ) + δ
  have hp : 0 ≤ p := by dsimp [p]; positivity
  obtain ⟨C, hC, hbudget⟩ := ScaledFiniteCoverBudget.exists_constant L (M * d) ((d - 1) * d) A p q hA hp
  refine ⟨max ((d - 1) * d) (M * d), C, hC, ?_⟩
  intro s hlen cZ I J hs hdeg hd hne hI hJ H hH hshifts U hU
  let c : Fin s.length → ℚ := fun i ↦ (cZ i : ℚ)
  have hc : ∀ i, c i ≠ 0 := fun i ↦ Int.cast_ne_zero.mpr (hd i)
  subst k
  let := sourceGrading c D I J hdeg hD
  obtain ⟨u, Q, _hu, hideal, _hirr, hgeom, hhom, htotal, hmonic, hpoints, htransfer⟩ :=
    ActualSourceSurfaceCoverReduction.exists_projection_with_cover_transfer s c D hD I J hs hdeg hc hne hI hJ
  let g := SourceSurfacePowerParameters.parameters s c D hD I J hs
  let y := primitive c D I J u
  let imageIdeal := LinearHypersurfaceImage.ideal (F := ℚ) g y
  have hImageHom : imageIdeal.IsHomogeneous (homogeneousSubmodule (Fin 4) ℚ) :=
    LinearHypersurfaceImage.ideal_homogeneous (sourcePiece c D I J) g
      (SourceSurfacePowerParameters.parameter_mem s c D hD I J hs) y
      (SourceImageIntegerPointEvaluation.primitive_mem s c D hD I J hdeg u)
  let := ActualSourceProjectedCurveFamilyCover.imageGrading s c D hD I J hs hdeg u
  let W := U.image (projection D u)
  have hW : W ⊆ UniformP3HypersurfaceCover.points Q (L * H) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hh := hpoints H w (hU hw)
    apply (UniformP3HypersurfaceCover.mem_points Q (L * H) _).mpr
    refine ⟨?_, hh.2.1, hh.2.2⟩
    intro i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hh.1 i
  have hLH : 1 ≤ L * H := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (heightFactor_pos s.length D).ne' (by omega))
  have hsupport : (SplitBranchPrimeCertificate.support I J).card ≤ s.length * (2 * D) :=
    by simpa only [Fintype.card_fin] using support_card_bound D I J hdeg
  have hshiftProjected : ∀ b ∈ SplitBranchPrimeCertificate.support I J,
      |b| ≤ (2 * (L * H) ^ 2 : ℕ) := by
    intro b hb
    apply (hshifts b hb).trans
    have hh : H ≤ L * H := by
      simpa only [one_mul] using Nat.mul_le_mul_right H (Nat.one_le_of_lt (heightFactor_pos s.length D))
    exact_mod_cast Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hh 2)
  obtain ⟨T, family, _hT, hM, hTbound, hfbound, hcover⟩ :=
    hP3 s rfl cZ I J hsupport hI hJ hne hs u Q hideal hgeom hhom hmonic
      imageIdeal hImageHom hideal (L * H) hLH hshiftProjected W hW
  obtain ⟨V, curves, hV, hVcount, hcount, hdegrees, hpoint⟩ := htransfer H U hU M T family hM (by
    intro v hv hnot
    exact hcover (projection D u v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hnot)
  have hb := hbudget H hH V.card curves.card T.card family.card hVcount hcount hTbound hfbound
  exact ⟨V, curves, hV, hdegrees, hb.1, hb.2, hpoint⟩

theorem cover_at_size (k D : ℕ) (hD : 0 < D) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧ IntegerExactSourceSurfaceCover.CoverAtSize k D hD B C δ := by
  classical
  obtain ⟨B, C, hC, hbounded⟩ := bounded_shifts_cover k D hD δ hδ
  let d := 2 ^ k * D ^ 2
  let C' : ℝ := C + (d : ℝ) + 1
  have hC' : 0 < C' := by dsimp only [C']; positivity
  have hCC : C ≤ C' := by dsimp only [C']; linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hdC : (d : ℝ) ≤ C' := by dsimp only [C']; linarith
  refine ⟨max B d, C', hC', ?_⟩
  intro s hlen cZ I J hs hdeg hd hne hI hJ H hH U hU
  by_cases hshifts : ∀ b ∈ SplitBranchPrimeCertificate.support I J, |b| ≤ (2 * H ^ 2 : ℕ)
  · obtain ⟨V, curves, hV, hdegree, hVbound, hcount, hpoint⟩ :=
      hbounded s hlen cZ I J hs hdeg hd hne hI hJ H hH hshifts U hU
    refine ⟨V, curves, hV, ?_, ?_, ?_, hpoint⟩
    · intro Γ hΓ
      exact (hdegree Γ hΓ).trans (by exact_mod_cast Nat.le_max_left B d)
    · exact hVbound.trans (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (Nat.cast_nonneg H) _))
    · exact hcount.trans (mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg (Nat.cast_nonneg H) _))
  · push Not at hshifts
    obtain ⟨a, ha, hlarge⟩ := hshifts
    obtain ⟨curves, hcard, hdegree, hpoint⟩ := LargeShiftSourceSectionCover.section_cover
      s cZ D I J hs hdeg hD hd hne hI hJ H hH a ha hlarge
    refine ⟨∅, curves, empty_subset U, ?_, ?_, ?_, ?_⟩
    · intro Γ hΓ
      have hh : degree s (fun i ↦ (cZ i : ℚ)) D I J hs hdeg hD Γ ≤ (d : ℚ) := by
        simpa only [d, hlen] using hdegree Γ hΓ
      exact hh.trans (by exact_mod_cast Nat.le_max_right B d)
    · simp only [card_empty, Nat.cast_zero]
      exact mul_nonneg hC'.le (Real.rpow_nonneg (Nat.cast_nonneg H) _)
    · have hcard' : (curves.card : ℝ) ≤ d := by
        exact_mod_cast (by simpa only [d, hlen] using hcard : curves.card ≤ d)
      have hpow : 1 ≤ (H : ℝ) ^ (1 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) :=
        Real.one_le_rpow (by exact_mod_cast hH) (by positivity)
      exact hcard'.trans (hdC.trans (by nlinarith))
    · intro v hv _hnot
      exact hpoint v (hU hv)

theorem uniform_cover (kmax D : ℕ) : IntegerExactSourceSurfaceCover.UniformCover kmax D := by
  classical
  intro δ hδ
  by_cases hD : 0 < D
  · have hsize (i : Fin (kmax + 1)) : ∃ (B : ℕ) (C : ℝ), 0 < C ∧ IntegerExactSourceSurfaceCover.CoverAtSize i.val D hD B C δ := by
      exact cover_at_size i.val D hD δ hδ
    choose B C hC hsize using hsize
    have hsum : 0 < ∑ i, C i := Finset.sum_pos (fun i _hi ↦ hC i) Finset.univ_nonempty
    refine ⟨Finset.univ.sup B, ∑ i, C i, hsum, ?_⟩
    intro hD' k hk
    let i : Fin (kmax + 1) := ⟨k, by omega⟩
    apply IntegerExactSourceSurfaceCover.CoverAtSize.mono (hsize i)
    · exact Finset.le_sup (f := B) (Finset.mem_univ i)
    · exact Finset.single_le_sum (fun j _hj ↦ (hC j).le) (Finset.mem_univ i)
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro hD'
    exact False.elim (hD hD')

end OriginalIntegerSourceCover
