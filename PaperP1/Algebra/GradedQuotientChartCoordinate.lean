module

public import PaperP1.Algebra.IrrelevantGenerated
public import PaperP1.Algebra.HomogeneousQuotientGrading

/-! # A relevant quotient of an algebra generated in degree one has a nonzero linear coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientChartCoordinate

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G]
  (hgen : Algebra.adjoin F (G 1 : Set A) = ⊤)
  (I : Ideal A) (hrel : ¬(HomogeneousIdeal.irrelevant G).toIdeal ≤ I)

include hgen hrel in
theorem exists_linear_outside : ∃ a : A, a ∈ G 1 ∧ a ∉ I := by
  by_contra! h
  apply hrel
  rw [IrrelevantGenerated.irrelevant_eq_span G (G 1 : Set A) (fun _ h ↦ h) hgen]
  exact Ideal.span_le.mpr h

include hgen hrel in
theorem exists_coordinate : ∃ b : A ⧸ I, b ∈ HomogeneousQuotientGrading.piece G I 1 ∧ b ≠ 0 := by
  obtain ⟨a, ha, hna⟩ := exists_linear_outside G hgen I hrel
  exact ⟨Ideal.Quotient.mk I a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩,
    fun hz ↦ hna (Ideal.Quotient.eq_zero_iff_mem.mp hz)⟩

end PaperP1.GradedQuotientChartCoordinate
