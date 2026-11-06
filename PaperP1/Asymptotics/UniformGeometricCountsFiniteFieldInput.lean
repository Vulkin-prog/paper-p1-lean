module

public import PaperP1.Asymptotics.UniformGeometricCountsAuxiliaryInput
public import PaperP1.Arithmetic.UniformP3AuxiliaryFromFiniteFieldCertificate

/-! # Companion T1.7 with only an independent finite-field good-prime certificate budget remaining -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsFiniteFieldInput

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemCertificates : ∀ k : ℕ, k ≤ p.systemSize →
    UniformP3FiniteFieldCertificate.UniformBudget (2 ^ k * p.systemDegree ^ 2)
  linearCertificates : ∀ k : ℕ, k ≤ p.linearSize →
    UniformP3FiniteFieldCertificate.UniformBudget (2 ^ k * (K + 1) ^ 2)
  typedCertificates : ∀ k : ℕ, k ≤ p.typedSize →
    UniformP3FiniteFieldCertificate.UniformBudget (2 ^ k * (a + 1 + 1) ^ 2)

theorem auxiliary_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsAuxiliaryInput.Hypotheses p K a where
  systemAuxiliary := fun k hk ↦ UniformP3AuxiliaryFromFiniteFieldCertificate.uniform_auxiliary _ (h.systemCertificates k hk)
  linearAuxiliary := fun k hk ↦ UniformP3AuxiliaryFromFiniteFieldCertificate.uniform_auxiliary _ (h.linearCertificates k hk)
  typedAuxiliary := fun k hk ↦ UniformP3AuxiliaryFromFiniteFieldCertificate.uniform_auxiliary _ (h.typedCertificates k hk)

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsAuxiliaryInput.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (auxiliary_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsFiniteFieldInput
