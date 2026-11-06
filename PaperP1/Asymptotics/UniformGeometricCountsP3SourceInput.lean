module

public import PaperP1.Asymptotics.UniformGeometricCountsSurfaceInputs
public import PaperP1.Arithmetic.SourceSurfaceCoverFromExactDegree

/-! # The chosen-source part of companion T1.7 now needs only the exact P³ input; both ordinary covers remain explicit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsP3SourceInput

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemHypersurfaces : ∀ k : ℕ, k ≤ p.systemSize →
    UniformP3HypersurfaceCover.UniformCover (2 ^ k * p.systemDegree ^ 2)
  linearCover : UniformOrdinarySurfaceCover.UniformCover p.linearSize K
  typedCover : UniformOrdinarySurfaceCover.UniformCover p.typedSize (a + 1)

theorem source_cover (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformSourceSurfaceCover.UniformCover p.systemSize K p.systemDegree :=
  SourceSurfaceCoverFromExactDegree.of_hypersurface_covers p.systemSize K p.systemDegree h.systemHypersurfaces

theorem surface_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsSurfaceInputs.Hypotheses p K a where
  systemCover := source_cover p K a h
  linearCover := h.linearCover
  typedCover := h.typedCover

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsSurfaceInputs.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (surface_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsP3SourceInput
