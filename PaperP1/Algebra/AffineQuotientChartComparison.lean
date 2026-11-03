module

public import PaperP1.Algebra.GradedDehomogenizationQuotient

/-! # Literal affine chart comparison from equality of the defining ideals after b=1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineQuotientChartComparison

open HomogeneousLocalization PaperP1.GradedDehomogenizationQuotient

variable {A : Type*} [CommRing A] (b : A) (I J : Ideal A)

theorem chartIdeal_map : (ideal b).map (Ideal.Quotient.mk I) = ideal (Ideal.Quotient.mk I b) := by
  simp only [ideal, Ideal.map_span, Set.image_singleton, map_sub, map_one]

def combinedEquiv : (A ⧸ I) ⧸ ideal (Ideal.Quotient.mk I b) ≃+* A ⧸ (I ⊔ ideal b) :=
  (Ideal.quotEquivOfEq (chartIdeal_map b I).symm).trans (DoubleQuot.quotQuotEquivQuotSup I (ideal b))

theorem combinedEquiv_mk (a : A) :
    combinedEquiv b I (Ideal.Quotient.mk _ (Ideal.Quotient.mk I a)) = Ideal.Quotient.mk (I ⊔ ideal b) a := by
  rw [combinedEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def quotientEquiv (h : I ⊔ ideal b = J ⊔ ideal b) :
    (A ⧸ I) ⧸ ideal (Ideal.Quotient.mk I b) ≃+* (A ⧸ J) ⧸ ideal (Ideal.Quotient.mk J b) :=
  ((combinedEquiv b I).trans (Ideal.quotEquivOfEq h)).trans (combinedEquiv b J).symm

theorem quotientEquiv_mk (h : I ⊔ ideal b = J ⊔ ideal b) (a : A) :
    quotientEquiv b I J h (Ideal.Quotient.mk _ (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (Ideal.Quotient.mk J a) := by
  rw [quotientEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, combinedEquiv_mk, Ideal.quotEquivOfEq_mk,
    ← combinedEquiv_mk b J a, RingEquiv.symm_apply_apply]

variable {σ τ : Type*} [SetLike σ (A ⧸ I)] [AddSubgroupClass σ (A ⧸ I)]
  [SetLike τ (A ⧸ J)] [AddSubgroupClass τ (A ⧸ J)]
  (G : ℕ → σ) (H : ℕ → τ) [GradedRing G] [GradedRing H]
  (hbI : Ideal.Quotient.mk I b ∈ G 1) (hbJ : Ideal.Quotient.mk J b ∈ H 1)

def chartEquiv (h : I ⊔ ideal b = J ⊔ ideal b) :
    Away G (Ideal.Quotient.mk I b) ≃+* Away H (Ideal.Quotient.mk J b) :=
  (((equiv G hbI).symm.trans (quotientEquiv b I J h)).trans (equiv H hbJ))

theorem chartEquiv_dehomogenization (h : I ⊔ ideal b = J ⊔ ideal b) (a : A) :
    chartEquiv b I J G H hbI hbJ h (GradedDehomogenization.map G hbI (Ideal.Quotient.mk I a)) =
      GradedDehomogenization.map H hbJ (Ideal.Quotient.mk J a) := by
  rw [chartEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, ← equiv_mk G hbI,
    RingEquiv.symm_apply_apply, quotientEquiv_mk, equiv_mk]

end PaperP1.AffineQuotientChartComparison
