module

public import PaperP1.Algebra.GradedDehomogenizationQuotient
public import PaperP1.Algebra.GradedSurjectiveChartMap

/-! # A surjective graded map gives the literal quotient of its affine chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientChartMap

open HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {G : ℕ → σ} {H : ℕ → τ} [GradedRing G] [GradedRing H]
  (f : G →+*ᵍ H) (hf : Function.Surjective f) {b : A} (hb : b ∈ G 1)

include hf in
theorem kernel : RingHom.ker (Away.map f b) =
    (RingHom.ker f.toRingHom).map (GradedDehomogenization.map G hb) := by
  apply Ideal.comap_injective_of_surjective (GradedDehomogenization.map G hb)
    (GradedDehomogenization.map_surjective G hb)
  rw [RingHom.comap_ker, GradedDehomogenization.map_natural G hb f,
    ← RingHom.comap_ker, GradedDehomogenizationQuotient.map_kernel H (f.map_mem hb)]
  have hspan : GradedDehomogenizationQuotient.ideal (f.toRingHom b) =
      (GradedDehomogenizationQuotient.ideal b).map f.toRingHom := by
    simp only [GradedDehomogenizationQuotient.ideal, Ideal.map_span, Set.image_singleton,
      map_sub, map_one]
  rw [hspan, Ideal.comap_map_of_surjective f.toRingHom hf,
    Ideal.comap_map_of_surjective _ (GradedDehomogenization.map_surjective G hb),
    ← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot,
    GradedDehomogenizationQuotient.map_kernel G hb, sup_comm]

def equiv : Away G b ⧸ (RingHom.ker f.toRingHom).map (GradedDehomogenization.map G hb) ≃+*
    Away H (f b) :=
  (Ideal.quotEquivOfEq (kernel f hf hb).symm).trans
    ((Away.map f b).quotientKerEquivOfSurjective
      (GradedSurjectiveChartMap.away_map_surjective f hf hb))

theorem equiv_mk (x : Away G b) :
    equiv f hf hb (Ideal.Quotient.mk _ x) = Away.map f b x := by
  rw [equiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

variable {R : Type*} [CommRing R]

def transportEquiv (e : Away G b ≃+* R) : Away H (f b) ≃+*
    R ⧸ (RingHom.ker f.toRingHom).map (e.toRingHom.comp (GradedDehomogenization.map G hb)) :=
  (equiv f hf hb).symm.trans
    (Ideal.quotientEquiv _ _ e (Ideal.map_map _ _).symm)

theorem transportEquiv_map (e : Away G b ≃+* R) (x : Away G b) :
    transportEquiv f hf hb e (Away.map f b x) = Ideal.Quotient.mk _ (e x) := by
  rw [transportEquiv, RingEquiv.trans_apply, ← equiv_mk f hf hb x,
    RingEquiv.symm_apply_apply]
  rfl

end PaperP1.GradedQuotientChartMap
