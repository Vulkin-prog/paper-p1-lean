module

public import PaperP1.Arithmetic.ActualSourceSurfaceCoverReduction
public import PaperP1.Arithmetic.UniformP3HypersurfaceCover
public import PaperP1.Asymptotics.ScaledFiniteCoverBudget

/-! # The exact P³ input implies coefficient-uniform source covers at the full genuine-degree exponents -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceCoverUnderP3

open MvPolynomial HomogeneousSplitRadicalData SourceProjectiveEmbedding SourceVeroneseGrading
  SourceSurfaceBoundedProjection SourceIntegerHypersurfaceProjection SourceProjectiveCurveData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _
attribute [local instance] MvPolynomial.gradedAlgebra

theorem of_cover_at_degree (k D : ℕ) (hD : 0 < D) (δ : ℝ) (hδ : 0 < δ)
    (M : ℕ) (A : ℝ) (hA : 0 < A)
    (hP3 : UniformP3HypersurfaceCover.CoverAtDegree (2 ^ k * D ^ 2) M A δ) :
    ∃ (B : ℕ) (C : ℝ), 0 < C ∧
      ∀ (s : List (PolynomialRing ℚ)), s.length = k →
      ∀ (c : Fin s.length → ℚ) (I J : Fin s.length → Finset ℤ)
        (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
        (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D),
        (∀ i, c i ≠ 0) → (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
        (Pairwise fun i j ↦ Disjoint (I i) (I j)) → (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      ∀ H : ℕ, 1 ≤ H → ∀ U : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ),
        U ⊆ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H →
        ∃ (V : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ))
            (curves : Finset (Curve s c D I J hdeg hD)),
          V ⊆ U ∧ (∀ Γ ∈ curves, degree s c D I J hs hdeg hD Γ ≤ (B : ℚ)) ∧
          (V.card : ℝ) ≤ C * (H : ℝ) ^ (2 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) ∧
          (curves.card : ℝ) ≤ C * (H : ℝ) ^ (1 / Real.sqrt ((2 ^ k * D ^ 2 : ℕ) : ℝ) + δ) ∧
          ∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves,
            v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s c D I J hdeg hD Γ) H := by
  classical
  let d := 2 ^ k * D ^ 2
  let L := heightFactor k D
  let p := 1 / Real.sqrt (d : ℝ) + δ
  let q := 2 / Real.sqrt (d : ℝ) + δ
  have hp : 0 ≤ p := by dsimp [p]; positivity
  obtain ⟨C, hC, hbudget⟩ := ScaledFiniteCoverBudget.exists_constant L (M * d) ((d - 1) * d) A p q hA hp
  refine ⟨max ((d - 1) * d) (M * d), C, hC, ?_⟩
  intro s hlen c I J hs hdeg hc hne hI hJ H hH U hU
  subst k
  let := sourceGrading c D I J hdeg hD
  obtain ⟨u, Q, _hu, hideal, _hirr, hgeom, hhom, htotal, _hmonic, hpoints, htransfer⟩ :=
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
  obtain ⟨T, family, _hT, hM, hTbound, hfbound, hcover⟩ :=
    hP3 imageIdeal hImageHom Q hideal hgeom hhom htotal (L * H) hLH W hW
  obtain ⟨V, curves, hV, hVcount, hcount, hdegrees, hpoint⟩ := htransfer H U hU M T family hM (by
    intro v hv hnot
    exact hcover (projection D u v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩) hnot)
  have hb := hbudget H hH V.card curves.card T.card family.card hVcount hcount hTbound hfbound
  exact ⟨V, curves, hV, hdegrees, hb.1, hb.2, hpoint⟩

end PaperP1.SourceSurfaceCoverUnderP3
