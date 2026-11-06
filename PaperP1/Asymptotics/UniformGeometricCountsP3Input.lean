module

public import PaperP1.Asymptotics.UniformGeometricCountsP3SourceInput
public import PaperP1.Arithmetic.UniformOrdinarySurfaceCoverFromExactSource

/-! # All source and ordinary geometric-cover translations in companion T1.7 are internal; only the exact P3 theorem remains -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsP3Input

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemHypersurfaces : ∀ k : ℕ, k ≤ p.systemSize →
    UniformP3HypersurfaceCover.UniformCover (2 ^ k * p.systemDegree ^ 2)
  linearHypersurfaces : ∀ k : ℕ, k ≤ p.linearSize →
    UniformP3HypersurfaceCover.UniformCover (2 ^ k * (K + 1) ^ 2)
  typedHypersurfaces : ∀ k : ℕ, k ≤ p.typedSize →
    UniformP3HypersurfaceCover.UniformCover (2 ^ k * (a + 1 + 1) ^ 2)

theorem linear_cover (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformOrdinarySurfaceCover.UniformCover p.linearSize K :=
  UniformOrdinarySurfaceCoverFromExactSource.of_hypersurface_covers p.linearSize K h.linearHypersurfaces

theorem typed_cover (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformOrdinarySurfaceCover.UniformCover p.typedSize (a + 1) :=
  UniformOrdinarySurfaceCoverFromExactSource.of_hypersurface_covers p.typedSize (a + 1) h.typedHypersurfaces

theorem source_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsP3SourceInput.Hypotheses p K a where
  systemHypersurfaces := h.systemHypersurfaces
  linearCover := linear_cover p K a h
  typedCover := typed_cover p K a h

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsP3SourceInput.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (source_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsP3Input
