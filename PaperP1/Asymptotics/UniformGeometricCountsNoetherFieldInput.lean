module

public import PaperP1.Asymptotics.UniformGeometricCountsFiniteFieldInput
public import PaperP1.Arithmetic.P3CertificateFromNoetherForms

/-! # Companion T1.7 with precisely the independent universal-form and finite-field estimate inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsNoetherFieldInput

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemForms : ∀ k : ℕ, k ≤ p.systemSize →
    P3UniversalNoetherForms.ExistsForms (2 ^ k * p.systemDegree ^ 2)
  systemEstimates : ∀ k : ℕ, k ≤ p.systemSize →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * p.systemDegree ^ 2)
  linearForms : ∀ k : ℕ, k ≤ p.linearSize →
    P3UniversalNoetherForms.ExistsForms (2 ^ k * (K + 1) ^ 2)
  linearEstimates : ∀ k : ℕ, k ≤ p.linearSize →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * (K + 1) ^ 2)
  typedForms : ∀ k : ℕ, k ≤ p.typedSize →
    P3UniversalNoetherForms.ExistsForms (2 ^ k * (a + 1 + 1) ^ 2)
  typedEstimates : ∀ k : ℕ, k ≤ p.typedSize →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * (a + 1 + 1) ^ 2)

theorem certificate_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsFiniteFieldInput.Hypotheses p K a where
  systemCertificates := fun k hk ↦ P3CertificateFromNoetherForms.uniform_budget _ (h.systemForms k hk) (h.systemEstimates k hk)
  linearCertificates := fun k hk ↦ P3CertificateFromNoetherForms.uniform_budget _ (h.linearForms k hk) (h.linearEstimates k hk)
  typedCertificates := fun k hk ↦ P3CertificateFromNoetherForms.uniform_budget _ (h.typedForms k hk) (h.typedEstimates k hk)

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsFiniteFieldInput.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (certificate_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsNoetherFieldInput
