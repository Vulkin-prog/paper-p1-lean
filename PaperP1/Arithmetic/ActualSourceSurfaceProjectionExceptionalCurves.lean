module

public import PaperP1.Geometry.SourceSurfaceComponentDegreeBudget
public import PaperP1.Arithmetic.SourceIntegerHypersurfaceProjection
public import PaperP1.Geometry.SourceSurfaceGeometricImage
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # One exact source projection has a fixed uniformly bounded exceptional-curve family before all heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSourceSurfaceProjectionExceptionalCurves

open MvPolynomial HomogeneousSplitRadicalData SourceProjectiveEmbedding
  SourceSurfaceBoundedProjection SourceIntegerHypersurfaceProjection

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) := index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

theorem exists_projection (s : List (PolynomialRing ℚ)) (c : Fin s.length → ℚ)
    (D : ℕ) (hD : 0 < D) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    ∃ (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) (q : MvPolynomial (Fin 4) ℚ)
        (curves : Finset (SourceProjectiveCurveData.Curve s c D I J hdeg hD)),
      (∀ i, u i ≤ coefficientBound s.length D) ∧ Irreducible q ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q) ∧
      q.IsHomogeneous (2 ^ s.length * D ^ 2) ∧ q.totalDegree = 2 ^ s.length * D ^ 2 ∧
      (finSuccEquiv ℚ 3 q).Monic ∧
      curves.card ≤ (2 ^ s.length * D ^ 2 - 1) * (2 ^ s.length * D ^ 2) ∧
      (∀ Γ ∈ curves, SourceProjectiveCurveData.degree s c D I J hs hdeg hD Γ ≤
        (((2 ^ s.length * D ^ 2 - 1) * (2 ^ s.length * D ^ 2) : ℕ) : ℚ)) ∧
      ∀ (H : ℕ) (v : GeneratorIndex ℚ (Fin s.length) D → ℤ),
        v ∈ SourceIntegerPoints.curvePoints D
          (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H →
        (∀ i, (projection D u v i).natAbs ≤ heightFactor s.length D * H) ∧
        projection D u v 3 = 1 ∧ eval (fun i ↦ (projection D u v i : ℚ)) q = 0 ∧
        (eval (fun i ↦ (projection D u v i : ℚ)) (pderiv 0 q) = 0 →
          ∃ Γ ∈ curves, v ∈ SourceIntegerPoints.curvePoints D
            (SourceProjectiveCurveData.ideal s c D I J hdeg hD Γ) H) ∧
        ∀ (w : GeneratorIndex ℚ (Fin s.length) D → ℤ),
          w ∈ SourceIntegerPoints.curvePoints D
            (RingHom.ker (SourceProjectiveEmbedding.evaluation c D I J hdeg hD).toRingHom) H →
          projection D u v = projection D u w →
          eval (fun i ↦ (projection D u v i : ℚ)) (pderiv 0 q) ≠ 0 → v = w := by
  obtain ⟨u, q, δ, hu, hideal, hirr, hhom, htotal, hmonic, _hrank, hpartial,
      hδmem, hδ0, hconductor, hheight⟩ :=
    SourceSurfaceBoundedProjection.exists_projection s c D hD I J hs hdeg hc hne hI hJ
  have hgeom := SourceSurfaceGeometricImage.source_irreducible_after_extension
    (E := AlgebraicClosure ℚ) s.length D c I J hc hne hI hJ
    (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u) q hideal hirr.ne_zero
  obtain ⟨curves, hcount, hdegrees, hcover⟩ :=
    SourceSurfaceComponentDegreeBudget.uniform_section_curve_cover s c D I J hs hdeg hD hc hne hI hJ
      (2 ^ s.length * D ^ 2 - 1) δ hδmem hδ0
  refine ⟨u, q, curves, hu, hirr, hgeom, hhom, htotal, hmonic, hcount,
    (fun Γ hΓ ↦ (hdegrees Γ hΓ).2), ?_⟩
  intro H v hv
  have hvalid := SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H v hv
  have hbox := (SourceIntegerPoints.mem_curvePoints _ _ _ _).mp hv |>.1
  have hvheight : ∀ i, (v i).natAbs ≤ H := by
    intro i
    have hh := hbox.1 i
    rw [Int.abs_eq_natAbs] at hh
    exact_mod_cast hh
  have hqmem : q ∈ LinearHypersurfaceImage.ideal (F := ℚ)
      (SourceSurfacePowerParameters.parameters s c D hD I J hs) (primitive c D I J u) := by
    rw [hideal]
    exact Ideal.mem_span_singleton_self q
  refine ⟨height D u v (heightFactor s.length D) H
    (Nat.one_le_iff_ne_zero.mpr (heightFactor_pos s.length D).ne') hvheight
    (hheight H v hvheight), normalized D u v hbox.2,
    on_equation s c D hD I J hs hdeg u v hvalid q hqmem, ?_, ?_⟩
  · intro hzero
    apply hcover H v hv
    rw [derivative_evaluation s c D hD I J hs hdeg u q δ hpartial v hvalid]
    exact hzero
  · intro w hw he hderiv
    have hwvalid := SourceIntegerPointEvaluation.valid_of_mem c D I J hdeg hD H w hw
    have hδ : SourceIntegerPointEvaluation.evaluation c D I J hdeg hD v hvalid δ ≠ 0 := by
      rw [derivative_evaluation s c D hD I J hs hdeg u q δ hpartial v hvalid]
      exact hderiv
    exact points_equal s c D hD I J hs hdeg u δ hconductor v w hvalid hwvalid he hδ

end PaperP1.ActualSourceSurfaceProjectionExceptionalCurves
