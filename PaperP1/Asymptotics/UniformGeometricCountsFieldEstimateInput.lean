module

public import PaperP1.Asymptotics.UniformGeometricCountsHigherDegreeInput
public import PaperP1.Arithmetic.P3UniversalNoetherFormsExistence

/-! # Companion T1.7 now requires only the independent higher-degree finite-field point estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsFieldEstimateInput

open UniformGeometricCountStatement

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemEstimates : ∀ k : ℕ, k ≤ p.systemSize → 2 < 2 ^ k * p.systemDegree ^ 2 →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * p.systemDegree ^ 2)
  linearEstimates : ∀ k : ℕ, k ≤ p.linearSize → 2 < 2 ^ k * (K + 1) ^ 2 →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * (K + 1) ^ 2)
  typedEstimates : ∀ k : ℕ, k ≤ p.typedSize → 2 < 2 ^ k * (a + 1 + 1) ^ 2 →
    P3FiniteFieldClassEstimate.UniformEstimate (2 ^ k * (a + 1 + 1) ^ 2)

theorem certificate_of_higher_estimate (d : ℕ)
    (hestimate : 2 < d → P3FiniteFieldClassEstimate.UniformEstimate d) :
    UniformP3FiniteFieldCertificate.UniformBudget d := by
  by_cases hd : d ≤ 2
  · exact P3QuadricFiniteFieldCertificate.of_degree_le_two d hd
  · exact P3CertificateFromNoetherForms.uniform_budget d
      (P3UniversalNoetherFormsExistence.exists_forms d) (hestimate (Nat.lt_of_not_ge hd))

theorem higher_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsHigherDegreeInput.Hypotheses p K a where
  systemForms := fun _ _ _ ↦ P3UniversalNoetherFormsExistence.exists_forms _
  systemEstimates := h.systemEstimates
  linearForms := fun _ _ _ ↦ P3UniversalNoetherFormsExistence.exists_forms _
  linearEstimates := h.linearEstimates
  typedForms := fun _ _ _ ↦ P3UniversalNoetherFormsExistence.exists_forms _
  typedEstimates := h.typedEstimates

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsHigherDegreeInput.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (higher_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsFieldEstimateInput
