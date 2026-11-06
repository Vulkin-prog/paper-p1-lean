module

public import PaperP1.Algebra.GradedDehomogenizationQuotient

/-! # Normalized graded points evaluate the literal degree-one affine chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedGradedPoint
open HomogeneousLocalization
variable {A B σ : Type*} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] {b : A} (hb : b ∈ G 1) (φ : A →+* B) (hn : φ b = 1)

def evaluation : Away G b →+* B :=
  (Ideal.Quotient.lift (PaperP1.GradedDehomogenizationQuotient.ideal b) φ (by
    change PaperP1.GradedDehomogenizationQuotient.ideal b ≤ RingHom.ker φ
    rw [PaperP1.GradedDehomogenizationQuotient.ideal, Ideal.span_singleton_le_iff_mem,
      RingHom.mem_ker, map_sub, map_one, hn, sub_self])).comp
    (PaperP1.GradedDehomogenizationQuotient.equiv G hb).symm.toRingHom

theorem evaluation_dehomogenization (x : A) :
    evaluation G hb φ hn (PaperP1.GradedDehomogenization.map G hb x) = φ x := by
  rw [← PaperP1.GradedDehomogenizationQuotient.equiv_mk G hb]
  simp [evaluation]

end NormalizedGradedPoint
