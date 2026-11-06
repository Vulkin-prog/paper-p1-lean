module

public import PaperP1.Asymptotics.UniformGeometricCountsP3Input
public import PaperP1.Arithmetic.UniformP3CoverFromAuxiliary

/-! # Companion T1.7 with only the explicit quantitative global auxiliary-equation input remaining -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsAuxiliaryInput

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemAuxiliary : ∀ k : ℕ, k ≤ p.systemSize →
    UniformP3AuxiliaryHypersurface.UniformAuxiliary (2 ^ k * p.systemDegree ^ 2)
  linearAuxiliary : ∀ k : ℕ, k ≤ p.linearSize →
    UniformP3AuxiliaryHypersurface.UniformAuxiliary (2 ^ k * (K + 1) ^ 2)
  typedAuxiliary : ∀ k : ℕ, k ≤ p.typedSize →
    UniformP3AuxiliaryHypersurface.UniformAuxiliary (2 ^ k * (a + 1 + 1) ^ 2)

theorem p3_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsP3Input.Hypotheses p K a where
  systemHypersurfaces := fun k hk ↦ UniformP3CoverFromAuxiliary.uniformCover _ (h.systemAuxiliary k hk)
  linearHypersurfaces := fun k hk ↦ UniformP3CoverFromAuxiliary.uniformCover _ (h.linearAuxiliary k hk)
  typedHypersurfaces := fun k hk ↦ UniformP3CoverFromAuxiliary.uniformCover _ (h.typedAuxiliary k hk)

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsP3Input.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (p3_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsAuxiliaryInput
