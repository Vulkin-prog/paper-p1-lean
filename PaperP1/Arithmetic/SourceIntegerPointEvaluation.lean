module

public import PaperP1.Geometry.GeneratedAlgebraPointEvaluation
public import PaperP1.Arithmetic.SourceIntegerPoints

/-! # Literal integer solutions of the chosen-embedding ideal evaluate the actual source algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerPointEvaluation

open MvPolynomial HomogeneousSplitRadicalVeronese SourceVeroneseGrading SourceProjectiveEmbedding

variable {ι : Type} (c : ι → ℚ) (D : ℕ) (I J : ι → Finset ℤ)

def Valid (v : GeneratorIndex ℚ ι D → ℤ) : Prop :=
  ∀ P ∈ GradedPolynomialPresentation.kernel (F := ℚ) (sourceGenerator c D I J),
    eval (fun i ↦ (v i : ℚ)) P = 0

def evaluation (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (v : GeneratorIndex ℚ ι D → ℤ) (hv : Valid c D I J v) : veronese c D I J →ₐ[ℚ] ℚ := by
  let := sourceGrading c D I J hdeg hD
  exact GeneratedAlgebraPointEvaluation.evaluation (sourcePiece c D I J)
    (sourceGenerator c D I J) (sourceGenerator_mem_one c D I J)
    (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J) (fun i ↦ (v i : ℚ)) hv

theorem evaluation_polynomial (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (v : GeneratorIndex ℚ ι D → ℤ) (hv : Valid c D I J v)
    (P : MvPolynomial (GeneratorIndex ℚ ι D) ℚ) :
    evaluation c D I J hdeg hD v hv (aeval (R := ℚ) (sourceGenerator c D I J) P) =
      eval (fun i ↦ (v i : ℚ)) P := by
  let := sourceGrading c D I J hdeg hD
  exact GeneratedAlgebraPointEvaluation.evaluation_polynomial (sourcePiece c D I J)
    (sourceGenerator c D I J) (sourceGenerator_mem_one c D I J)
    (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J) _ hv P

theorem evaluation_coordinate (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (v : GeneratorIndex ℚ ι D → ℤ) (hv : Valid c D I J v) (i : GeneratorIndex ℚ ι D) :
    evaluation c D I J hdeg hD v hv (sourceGenerator c D I J i) = (v i : ℚ) := by
  simpa only [aeval_X, eval_X] using evaluation_polynomial c D I J hdeg hD v hv (X i)

theorem points_equal (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (v w : GeneratorIndex ℚ ι D → ℤ) (hv : Valid c D I J v) (hw : Valid c D I J w)
    (he : evaluation c D I J hdeg hD v hv = evaluation c D I J hdeg hD w hw) : v = w := by
  funext i
  have hh := DFunLike.congr_fun he (sourceGenerator c D I J i)
  simp only [evaluation_coordinate] at hh
  exact Int.cast_injective hh

theorem valid_of_mem [Finite ι] (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)
    (H : ℕ) (v : GeneratorIndex ℚ ι D → ℤ)
    (hv : v ∈ SourceIntegerPoints.curvePoints D
      (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H) :
    Valid c D I J v := by
  intro P hP
  exact (SourceIntegerPoints.mem_curvePoints _ _ _ _).mp hv |>.2 hP

end PaperP1.SourceIntegerPointEvaluation
