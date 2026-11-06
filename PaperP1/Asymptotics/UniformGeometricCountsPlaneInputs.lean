module

public import PaperP1.Asymptotics.UniformGeometricCountsFieldEstimateInput
public import PaperP1.Arithmetic.P3PointEstimateFromPlaneInputs

/-! # An alternative exact companion T1.7 derivation from two explicit classical plane inputs

The good-section and plane-curve estimates remain unproved hypotheses.
The existing canonical one-input theorem is retained unchanged.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricCountsPlaneInputs

open UniformGeometricCountStatement P3ClassicalPlanePointInputs

structure Hypotheses (p : Parameters) (K a : ℕ) : Prop where
  systemCurves : ∀ k : ℕ, k ≤ p.systemSize → 2 < 2 ^ k * p.systemDegree ^ 2 →
    PlaneCurveUpperBound (2 ^ k * p.systemDegree ^ 2)
  systemSections : ∀ k : ℕ, k ≤ p.systemSize → 2 < 2 ^ k * p.systemDegree ^ 2 →
    GoodGraphSection (2 ^ k * p.systemDegree ^ 2)
  linearCurves : ∀ k : ℕ, k ≤ p.linearSize → 2 < 2 ^ k * (K + 1) ^ 2 →
    PlaneCurveUpperBound (2 ^ k * (K + 1) ^ 2)
  linearSections : ∀ k : ℕ, k ≤ p.linearSize → 2 < 2 ^ k * (K + 1) ^ 2 →
    GoodGraphSection (2 ^ k * (K + 1) ^ 2)
  typedCurves : ∀ k : ℕ, k ≤ p.typedSize → 2 < 2 ^ k * (a + 1 + 1) ^ 2 →
    PlaneCurveUpperBound (2 ^ k * (a + 1 + 1) ^ 2)
  typedSections : ∀ k : ℕ, k ≤ p.typedSize → 2 < 2 ^ k * (a + 1 + 1) ^ 2 →
    GoodGraphSection (2 ^ k * (a + 1 + 1) ^ 2)

theorem estimate_of_inputs (d : ℕ) (hd : 2 < d)
    (hcurve : PlaneCurveUpperBound d) (hsection : GoodGraphSection d) :
    P3FiniteFieldClassEstimate.UniformEstimate d :=
  P3PointEstimateFromPlaneInputs.uniform_estimate d (by omega) hcurve hsection

theorem field_hypotheses (p : Parameters) (K a : ℕ) (h : Hypotheses p K a) :
    UniformGeometricCountsFieldEstimateInput.Hypotheses p K a where
  systemEstimates := fun k hk hd ↦ estimate_of_inputs _ hd (h.systemCurves k hk hd) (h.systemSections k hk hd)
  linearEstimates := fun k hk hd ↦ estimate_of_inputs _ hd (h.linearCurves k hk hd) (h.linearSections k hk hd)
  typedEstimates := fun k hk hd ↦ estimate_of_inputs _ hd (h.typedCurves k hk hd) (h.typedSections k hk hd)

theorem companion_T1_7 (C A₀ ε η : ℝ) (K Jexp a : ℕ)
    (hA₀ : 0 ≤ A₀) (hε : 0 < ε) (hη : 0 < η) (ha : 0 < a) :
    ∃ p : Parameters, 0 < p.systemDegree ∧ 0 < p.denseDegree ∧ 1 ≤ p.linearSize ∧
      (Hypotheses p K a → Assertions C A₀ ε η K Jexp a p) := by
  obtain ⟨p, hD, hdense, hlinear, hproof⟩ :=
    UniformGeometricCountsFieldEstimateInput.companion_T1_7 C A₀ ε η K Jexp a hA₀ hε hη ha
  exact ⟨p, hD, hdense, hlinear, fun h ↦ hproof (field_hypotheses p K a h)⟩

end PaperP1.UniformGeometricCountsPlaneInputs
