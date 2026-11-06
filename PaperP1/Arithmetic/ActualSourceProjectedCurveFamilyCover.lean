module

public import PaperP1.Arithmetic.ActualSourceProjectedCurveCover
public import PaperP1.Geometry.GradedProjectiveCurveData
public import PaperP1.Arithmetic.SourceImageIntegerPointEvaluation

/-! # The whole finite projected-curve family lifts before all source heights with explicit count and degree bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceProjectedCurveFamilyCover

open MvPolynomial HomogeneousSplitRadicalData SourceVeroneseGrading SourceProjectiveEmbedding
  SourceProjectiveCurveData SourceSurfaceBoundedProjection LinearHypersurfaceImage

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
  (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
  (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
  (u : GeneratorIndex ℚ (Fin s.length) D → ℕ)

@[instance_reducible]
def imageGrading : GradedAlgebra (piece (F := ℚ)
    (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u)) := by
  let := sourceGrading c D I J hdeg hD
  exact grading (sourcePiece c D I J) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
    (SourceSurfacePowerParameters.parameter_mem s c D hD I J hs) (primitive c D I J u)
    (SourceImageIntegerPointEvaluation.primitive_mem s c D hD I J hdeg u)

include hc hne hI hJ

theorem uniform_family_cover :
    letI := imageGrading s c D hD I J hs hdeg u;
    ∀ (family : Finset (GradedProjectiveCurveData.Curve (piece (F := ℚ)
      (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u))))
    (M : ℕ) (_hM : ∀ Γ ∈ family, Γ.degree ≤ (M : ℚ)),
    ∃ curves : Finset (Curve s c D I J hdeg hD),
      curves.card ≤ family.card * (M * (2 ^ s.length * D ^ 2)) ∧
      (∀ Γ ∈ curves, degree s c D I J hs hdeg hD Γ ≤ ((M * (2 ^ s.length * D ^ 2) : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
        (_hv : v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H),
        (∃ Γ ∈ family, ∀ P ∈ SourceImageIntegerPointEvaluation.imageIdeal s c D hD I J hs u Γ.ideal,
          eval (fun i ↦ (SourceIntegerHypersurfaceProjection.projection D u v i : ℚ)) P = 0) →
        ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D (SourceProjectiveCurveData.ideal s c D I J hdeg hD Γ) H := by
  classical
  let := sourceGrading c D I J hdeg hD
  let := imageGrading s c D hD I J hs hdeg u
  intro family M hM
  have hsingle (Γ : family) :=
    letI : Γ.val.ideal.IsPrime := Γ.val.ideal_prime
    ActualSourceProjectedCurveCover.uniform_curve_cover s c D hD I J hs hdeg hc hne hI hJ u
      Γ.val.ideal Γ.val.ideal_homogeneous Γ.val.ideal_height Γ.val.degree Γ.val.constant Γ.val.hilbert M
      (hM Γ.val Γ.property)
  choose C hC using hsingle
  let curves := Finset.univ.biUnion C
  refine ⟨curves, ?_, ?_, ?_⟩
  · calc
      curves.card ≤ ∑ Γ : family, (C Γ).card := Finset.card_biUnion_le
      _ ≤ ∑ _Γ : family, M * (2 ^ s.length * D ^ 2) := Finset.sum_le_sum (fun Γ _hΓ ↦ (hC Γ).1)
      _ = family.card * (M * (2 ^ s.length * D ^ 2)) := by simp
  · intro Δ hΔ
    obtain ⟨Γ, _hΓ, hΔΓ⟩ := Finset.mem_biUnion.mp hΔ
    exact (hC Γ).2.1 Δ hΔΓ
  · intro H v hv hpoint
    obtain ⟨Γ, hΓ, hvanish⟩ := hpoint
    let Γ' : family := ⟨Γ, hΓ⟩
    obtain ⟨Δ, hΔ, hvΔ⟩ := (hC Γ').2.2 H v hv hvanish
    exact ⟨Δ, Finset.mem_biUnion.mpr ⟨Γ', Finset.mem_univ _, hΔ⟩, hvΔ⟩

end PaperP1.ActualSourceProjectedCurveFamilyCover
