module

public import PaperP1.Arithmetic.P3UniversalGoodReduction
public import PaperP1.Arithmetic.UniformP3FiniteFieldCertificate

/-! # The algebraic certificate height constants precede every finite-field error tolerance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FiniteFieldBudgetFixedHeight

open MvPolynomial

theorem fixed_height_constants (d : ℕ) :
    ∃ T N : ℕ, 0 < T ∧ ∀ η : ℝ, 0 < η →
      (P3FiniteFieldClassEstimate.UniformEstimate d →
        ∃ K₀ : ℕ, UniformP3FiniteFieldCertificate.AtDegree d (1 + η) T N K₀) := by
  obtain ⟨T, N, hT, hcert⟩ := P3UniversalGoodReduction.bounded_certificate d
  refine ⟨T, N, hT, ?_⟩
  intro η hη hestimate
  obtain ⟨K₀, hpoint⟩ := hestimate η hη
  refine ⟨K₀, ?_⟩
  intro A hA P hgeom hhom hcoef
  obtain ⟨z, hz, hbound, hgood⟩ := hcert A hA P hhom hgeom hcoef
  refine ⟨z, hz, hbound, ?_⟩
  intro p hp hK hnot
  exact hpoint p hp hK P hhom (P3UniversalGoodReduction.geometric_reduction P z hgood p hp hnot)

theorem uniform_budget (d : ℕ) (hestimate : P3FiniteFieldClassEstimate.UniformEstimate d) :
    UniformP3FiniteFieldCertificate.UniformBudget d := by
  obtain ⟨T, N, hT, h⟩ := fixed_height_constants d
  intro η hη
  obtain ⟨K₀, hK⟩ := h η hη hestimate
  exact ⟨T, N, K₀, hT, hK⟩

end PaperP1.P3FiniteFieldBudgetFixedHeight
