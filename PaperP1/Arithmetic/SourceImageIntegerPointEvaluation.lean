module

public import PaperP1.Arithmetic.SourceIntegerHypersurfaceProjection

/-! # The actual image-curve ideal vanishes exactly at the actual projected original integer point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceImageIntegerPointEvaluation

open MvPolynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading
  SourceProjectiveEmbedding SourceSurfaceBoundedProjection LinearHypersurfaceImage

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

variable (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (u : GeneratorIndex ℚ (Fin s.length) D → ℕ)

include hdeg hD in
theorem primitive_mem : primitive c D I J u ∈ sourcePiece c D I J 1 := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialGenerators.eval_homogeneous (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) 1 _ (CommonLinearNormalization.form_homogeneous _)

def imageEvaluation (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v) :
    CoordinateRing (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (primitive c D I J u) →ₐ[ℚ] ℚ :=
  (SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv).comp
    (toSource (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u))

def imageIdeal (Q : Ideal (CoordinateRing (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
    (primitive c D I J u))) : Ideal (MvPolynomial (Fin 4) ℚ) :=
  Q.comap (Ideal.Quotient.mk (ideal (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
    (primitive c D I J u)))

theorem imageEvaluation_mk (v : GeneratorIndex ℚ (Fin s.length) D → ℤ)
    (hv : SourceIntegerPointEvaluation.Valid c D I J v) (P : MvPolynomial (Fin 4) ℚ) :
    imageEvaluation s c D hD I J hs hdeg u v hv
      (Ideal.Quotient.mk (ideal (F := ℚ) (SourceSurfacePowerParameters.parameters s c D hD I J hs)
        (primitive c D I J u)) P) =
      eval (fun i ↦ (SourceIntegerHypersurfaceProjection.projection D u v i : ℚ)) P := by
  change SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hv
    (aeval (R := ℚ) (coordinates (SourceSurfacePowerParameters.parameters s c D hD I J hs)
      (primitive c D I J u)) P) = _
  exact SourceIntegerHypersurfaceProjection.evaluation_projected s c D hD I J hs hdeg u v hv P

theorem annihilates_iff (Q : Ideal (CoordinateRing (F := ℚ)
      (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u)))
    (v : GeneratorIndex ℚ (Fin s.length) D → ℤ) (hv : SourceIntegerPointEvaluation.Valid c D I J v) :
    Q ≤ RingHom.ker (imageEvaluation s c D hD I J hs hdeg u v hv).toRingHom ↔
      ∀ P ∈ imageIdeal s c D hD I J hs u Q,
        eval (fun i ↦ (SourceIntegerHypersurfaceProjection.projection D u v i : ℚ)) P = 0 := by
  constructor
  · intro hpoint P hP
    have hh := hpoint hP
    change imageEvaluation s c D hD I J hs hdeg u v hv (Ideal.Quotient.mk _ P) = 0 at hh
    rwa [imageEvaluation_mk] at hh
  · intro hpoint b hb
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
    change imageEvaluation s c D hD I J hs hdeg u v hv (Ideal.Quotient.mk _ P) = 0
    rw [imageEvaluation_mk]
    exact hpoint P hb

end PaperP1.SourceImageIntegerPointEvaluation
