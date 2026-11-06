module

public import PaperP1.Arithmetic.IntegerSourceCoverConsequences
public import PaperP1.Arithmetic.IntegerOrdinarySourceCover
public import PaperP1.Asymptotics.UniformGeometricCountsSurfaceInputs

/-! # The complete original companion T1.7 geometric counts with no external input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCounts
open PaperP1 UniformGeometricCountStatement

theorem surface_hypotheses (p : Parameters) (K a : ℕ) :
    UniformGeometricCountsSurfaceInputs.Hypotheses p K a where
  systemCover := IntegerSourceCoverConsequences.system_cover p.systemSize K p.systemDegree
  linearCover := IntegerOrdinarySourceCover.uniform_cover p.linearSize K
  typedCover := IntegerOrdinarySourceCover.uniform_cover p.typedSize (a + 1)

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      Assertions C A₀ ε η K Jexp a p := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsSurfaceInputs.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, hproof (surface_hypotheses p K a)⟩
end UniformGeometricCounts
