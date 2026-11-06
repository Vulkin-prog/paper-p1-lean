module

public import PaperP1.Asymptotics.UniformGeometricCountsReducedInputs
public import PaperP1.Arithmetic.UnconditionalNormalizedCurveCount

/-! # Companion T1.7 retains only its actual surface-cover inputs; all curve counts are internal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsSurfaceInputs

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemCover : UniformSourceSurfaceCover.UniformCover p.systemSize K p.systemDegree
  linearCover : UniformOrdinarySurfaceCover.UniformCover p.linearSize K
  typedCover : UniformOrdinarySurfaceCover.UniformCover p.typedSize (a + 1)

theorem reduced_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsReducedInputs.Hypotheses p K a where
  systemCover := h.systemCover
  systemCurves := fun M ↦ UnconditionalNormalizedCurveCount.uniform_bound
    ((p.systemDegree + 2).choose 2 + p.systemSize) M
  linearCover := h.linearCover
  linearCurves := fun M ↦ UnconditionalNormalizedCurveCount.uniform_bound (p.linearSize + 3) M
  typedCover := h.typedCover
  typedCurves := fun M ↦ UnconditionalNormalizedCurveCount.uniform_bound (p.typedSize + 3) M

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsReducedInputs.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (reduced_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsSurfaceInputs
