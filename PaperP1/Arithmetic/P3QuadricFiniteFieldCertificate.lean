module

public import PaperP1.Arithmetic.QuadricHessianGoodReduction
public import PaperP1.Arithmetic.P3QuadricFiniteFieldEstimate

/-! # The complete uniform finite-field certificate and global auxiliary theorem are proved in degree two -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3QuadricFiniteFieldCertificate

theorem uniform_budget : UniformP3FiniteFieldCertificate.UniformBudget 2 := by
  intro η hη
  obtain ⟨K₀, hK₀⟩ := P3QuadricFiniteFieldEstimate.uniform_estimate η hη
  refine ⟨48, 3, K₀, by decide, ?_⟩
  intro A _hA P hgeom hhom hcoef
  obtain ⟨z, hz, hbound, hgood⟩ := QuadricHessianGoodReduction.bounded_certificate A P hhom hgeom hcoef
  exact ⟨z, hz, hbound, fun p hp hK hnot ↦ hK₀ p hp hK P hhom (hgood p hp hnot)⟩

theorem of_degree_le_two (d : ℕ) (hd : d ≤ 2) : UniformP3FiniteFieldCertificate.UniformBudget d := by
  by_cases h : d ≤ 1
  · exact UniformP3FiniteFieldCertificate.of_degree_le_one d h
  · have he : d = 2 := by omega
    rw [he]
    exact uniform_budget

theorem uniform_auxiliary (d : ℕ) (hd : d ≤ 2) : UniformP3AuxiliaryHypersurface.UniformAuxiliary d :=
  UniformP3AuxiliaryFromFiniteFieldCertificate.uniform_auxiliary d (of_degree_le_two d hd)

end PaperP1.P3QuadricFiniteFieldCertificate
