module

public import PaperP1.Arithmetic.SourceIntegerPointEvaluation
public import PaperP1.Geometry.SourceSurfaceBoundedProjection
public import PaperP1.Algebra.SourceSurfacePowerCoordinates
public import PaperP1.Geometry.HypersurfaceImagePointSeparation

/-! # Literal normalized integer hypersurface coordinates, their actual source evaluations and good fibres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerHypersurfaceProjection

open MvPolynomial SourceProjectiveEmbedding HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese

variable {ι : Type} [Finite ι]

local instance indexFinite (D : ℕ) : Finite (GeneratorIndex ℚ ι D) := index_finite ℚ ι D
local instance indexFintype (D : ℕ) : Fintype (GeneratorIndex ℚ ι D) := Fintype.ofFinite _

def primitiveCoordinate (D : ℕ) (u : GeneratorIndex ℚ ι D → ℕ) (v : GeneratorIndex ℚ ι D → ℤ) : ℤ :=
  eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))

def projection (D : ℕ) (u : GeneratorIndex ℚ ι D → ℕ) (v : GeneratorIndex ℚ ι D → ℤ) : Fin 4 → ℤ :=
  Fin.cons (primitiveCoordinate D u v) (fun j ↦ v (SourceSurfacePowerCoordinates.index ℚ ι D j))

theorem primitive_cast (D : ℕ) (u : GeneratorIndex ℚ ι D → ℕ) (v : GeneratorIndex ℚ ι D → ℤ) :
    (primitiveCoordinate D u v : ℚ) =
      eval (fun i ↦ (v i : ℚ)) (CommonLinearNormalization.form (fun i ↦ (u i : ℚ))) := by
  simp only [primitiveCoordinate, CommonLinearNormalization.evaluation,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast]

theorem height (D : ℕ) (u : GeneratorIndex ℚ ι D → ℕ) (v : GeneratorIndex ℚ ι D → ℤ)
    (M H : ℕ) (hM : 1 ≤ M) (hv : ∀ i, (v i).natAbs ≤ H)
    (hprimitive : |primitiveCoordinate D u v| ≤ ((M * H : ℕ) : ℤ)) :
    ∀ i, (projection D u v i).natAbs ≤ M * H := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (primitiveCoordinate D u v).natAbs ≤ M * H
    rw [Int.abs_eq_natAbs] at hprimitive
    exact_mod_cast hprimitive
  · change (v (SourceSurfacePowerCoordinates.index ℚ ι D j)).natAbs ≤ M * H
    have hscale : H ≤ M * H := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right H hM
    exact (hv _).trans hscale

theorem normalized (D : ℕ) (u : GeneratorIndex ℚ ι D → ℕ) (v : GeneratorIndex ℚ ι D → ℤ)
    (hv : v (SourceIntegerPoints.normalizer D) = 1) : projection D u v 3 = 1 := by
  change v (SourceIntegerPoints.normalizer D) = 1
  exact hv

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (u : GeneratorIndex ℚ (Fin s.length) D → ℕ)

theorem evaluation_coordinates (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v) :
    ∀ i, SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (LinearHypersurfaceImage.coordinates (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfaceBoundedProjection.primitive c D I J u) i) = (projection D u v i : ℚ) := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (aeval (R := ℚ) (SourceVeroneseGrading.sourceGenerator c D I J)
        (CommonLinearNormalization.form (fun i ↦ (u i : ℚ)))) = (primitiveCoordinate D u v : ℚ)
    rw [SourceIntegerPointEvaluation.evaluation_polynomial, primitive_cast]
  · change SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (SourceSurfacePowerParameters.parameters s c D hD I J hs j) =
        (v (SourceSurfacePowerCoordinates.index ℚ (Fin s.length) D j) : ℚ)
    rw [← SourceSurfacePowerCoordinates.generator_eq s c D hD I J hs j,
      SourceIntegerPointEvaluation.evaluation_coordinate]

theorem evaluation_projected (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v) (P : MvPolynomial (Fin 4) ℚ) :
    SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (aeval (R := ℚ) (LinearHypersurfaceImage.coordinates
        (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfaceBoundedProjection.primitive c D I J u)) P) =
      eval (fun i ↦ (projection D u v i : ℚ)) P := by
  rw [comp_aeval_apply]
  change eval (fun i ↦ SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
    (LinearHypersurfaceImage.coordinates (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (SourceSurfaceBoundedProjection.primitive c D I J u) i)) P = _
  simp only [evaluation_coordinates]

include hdeg in
theorem on_equation (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v) (q : MvPolynomial (Fin 4) ℚ)
    (hq : q ∈ LinearHypersurfaceImage.ideal
      (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (SourceSurfaceBoundedProjection.primitive c D I J u)) :
    eval (fun i ↦ (projection D u v i : ℚ)) q = 0 := by
  have hzero : aeval (R := ℚ) (LinearHypersurfaceImage.coordinates
      (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (SourceSurfaceBoundedProjection.primitive c D I J u)) q = 0 := hq
  have hh := congrArg (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv) hzero
  rwa [map_zero, evaluation_projected] at hh

theorem derivative_evaluation (q : MvPolynomial (Fin 4) ℚ) (δ : veronese c D I J)
    (hδ : δ = aeval (R := ℚ) (LinearHypersurfaceImage.coordinates
      (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (SourceSurfaceBoundedProjection.primitive c D I J u)) (pderiv 0 q))
    (v : GeneratorIndex ℚ (Fin s.length) D → ℤ) (hv : SourceIntegerPointEvaluation.Valid c D I J v) :
    SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv δ =
      eval (fun i ↦ (projection D u v i : ℚ)) (pderiv 0 q) := by
  rw [hδ, evaluation_projected]

theorem points_equal (δ : veronese c D I J)
    (hconductor : ∀ a : veronese c D I J, δ * a ∈
      (LinearHypersurfaceImage.toSource (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfaceBoundedProjection.primitive c D I J u)).range)
    (v w : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v)
    (hw : SourceIntegerPointEvaluation.Valid c D I J w)
    (he : projection D u v = projection D u w)
    (hδ : SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv δ ≠ 0) : v = w := by
  have hcoords : ∀ i, SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
      (LinearHypersurfaceImage.coordinates (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfaceBoundedProjection.primitive c D I J u) i) =
      SourceIntegerPointEvaluation.evaluation c D I J hdeg hD w hw
        (LinearHypersurfaceImage.coordinates (SourceSurfacePowerParameters.parameters s c D hD I J hs)
          (SourceSurfaceBoundedProjection.primitive c D I J u) i) := by
    intro i
    rw [evaluation_coordinates, evaluation_coordinates, he]
  have hh := HypersurfaceImagePointSeparation.evaluations_equal_of_conductor
    (SourceSurfacePowerParameters.parameters s c D hD I J hs)
    (SourceSurfaceBoundedProjection.primitive c D I J u) δ hconductor
    (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv)
    (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD w hw) hcoords hδ
  exact SourceIntegerPointEvaluation.points_equal c D I J hdeg hD v w hv hw hh

theorem good_card_le (δ : veronese c D I J)
    (hconductor : ∀ a : veronese c D I J, δ * a ∈
      (LinearHypersurfaceImage.toSource (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (SourceSurfaceBoundedProjection.primitive c D I J u)).range)
    (S : Finset (GeneratorIndex ℚ (Fin s.length) D → ℤ)) (T : Finset (Fin 4 → ℤ))
    (hvalid : ∀ v ∈ S, SourceIntegerPointEvaluation.Valid c D I J v)
    (hgood : ∀ (v) (hv : v ∈ S), SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v (hvalid v hv) δ ≠ 0)
    (hmap : ∀ v ∈ S, projection D u v ∈ T) : S.card ≤ T.card := by
  classical
  have hinj : Set.InjOn (projection D u) (S : Set _) := by
    intro v hv w hw he
    exact points_equal s c D hD I J hs hdeg u δ hconductor v w (hvalid v hv) (hvalid w hw) he (hgood v hv)
  calc
    S.card = (S.image (projection D u)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ T.card := Finset.card_le_card (by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact hmap v hv)

end PaperP1.SourceIntegerHypersurfaceProjection
