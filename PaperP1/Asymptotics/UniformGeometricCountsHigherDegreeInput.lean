module

public import PaperP1.Asymptotics.UniformGeometricCountsNoetherFieldInput
public import PaperP1.Arithmetic.P3QuadricFiniteFieldCertificate

/-! # Companion T1.7 needs independent geometric inputs only in degrees strictly above two -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsHigherDegreeInput

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemForms : ∀ k : ℕ, k ≤ p.systemSize → 2 < 2 ^ k * p.systemDegree ^ 2 →
    P3UniversalNoetherForms.ExistsForms (2 ^ k * p.systemDegree ^ 2)
  systemEstimates : ∀ k : ℕ, k ≤ p.systemSize → 2 < 2 ^ k * p.systemDegree ^ 2 →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * p.systemDegree ^ 2)
  linearForms : ∀ k : ℕ, k ≤ p.linearSize → 2 < 2 ^ k * (K + 1) ^ 2 →
    P3UniversalNoetherForms.ExistsForms (2 ^ k * (K + 1) ^ 2)
  linearEstimates : ∀ k : ℕ, k ≤ p.linearSize → 2 < 2 ^ k * (K + 1) ^ 2 →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * (K + 1) ^ 2)
  typedForms : ∀ k : ℕ, k ≤ p.typedSize → 2 < 2 ^ k * (a + 1 + 1) ^ 2 →
    P3UniversalNoetherForms.ExistsForms (2 ^ k * (a + 1 + 1) ^ 2)
  typedEstimates : ∀ k : ℕ, k ≤ p.typedSize → 2 < 2 ^ k * (a + 1 + 1) ^ 2 →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * (a + 1 + 1) ^ 2)

theorem certificate_of_higher_inputs (d : ℕ)
    (hforms : 2 < d → P3UniversalNoetherForms.ExistsForms d)
    (hestimate : 2 < d → P3FiniteFieldClassEstimate.UniformEstimate d) :
    UniformP3FiniteFieldCertificate.UniformBudget d := by
  by_cases hd : d ≤ 2
  · exact P3QuadricFiniteFieldCertificate.of_degree_le_two d hd
  · have hlarge : 2 < d := Nat.lt_of_not_ge hd
    exact P3CertificateFromNoetherForms.uniform_budget d (hforms hlarge) (hestimate hlarge)

theorem certificate_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsFiniteFieldInput.Hypotheses p K a where
  systemCertificates := fun k hk ↦ certificate_of_higher_inputs _ (h.systemForms k hk) (h.systemEstimates k hk)
  linearCertificates := fun k hk ↦ certificate_of_higher_inputs _ (h.linearForms k hk) (h.linearEstimates k hk)
  typedCertificates := fun k hk ↦ certificate_of_higher_inputs _ (h.typedForms k hk) (h.typedEstimates k hk)

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsFiniteFieldInput.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (certificate_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsHigherDegreeInput
