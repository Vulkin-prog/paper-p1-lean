module

public import PaperP1.Algebra.GradedDehomogenization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # A degree-one homogeneous chart is the literal quotient by b - 1 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedDehomogenizationQuotient

open HomogeneousLocalization DirectSum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (G : ℕ → σ) [GradedRing G] {b : A} (hb : b ∈ G 1)

def ideal (b : A) : Ideal A := Ideal.span {b - 1}

theorem quotient_variable (b : A) : Ideal.Quotient.mk (ideal b) b = 1 := by
  have h : Ideal.Quotient.mk (ideal b) (b - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (b - 1))
  simpa only [map_sub, map_one, sub_eq_zero] using h

def fromLocalization (b : A) : Localization.Away b →+* A ⧸ ideal b :=
  Localization.awayLift (Ideal.Quotient.mk (ideal b)) b (by
    rw [quotient_variable]
    exact isUnit_one)

def toQuotient : Away G b →+* A ⧸ ideal b :=
  (fromLocalization b).comp (algebraMap (Away G b) (Localization.Away b))

theorem toQuotient_mk (n : ℕ) (x : A) (hx : x ∈ G (n • (1 : ℕ))) :
    toQuotient G (Away.mk G hb n x hx) = Ideal.Quotient.mk (ideal b) x := by
  change Localization.awayLift (Ideal.Quotient.mk (ideal b)) b
    (by rw [quotient_variable]; exact isUnit_one)
    (Localization.mk x ⟨b ^ n, n, rfl⟩) = _
  rw [Localization.awayLift_mk _ b x 1 (by simp only [quotient_variable, mul_one]) n]
  simp

theorem toQuotient_comp :
    (toQuotient G).comp (GradedDehomogenization.map G hb) = Ideal.Quotient.mk (ideal b) := by
  classical
  apply RingHom.ext
  intro x
  rw [← DirectSum.sum_support_decompose G x]
  simp only [map_sum, RingHom.comp_apply]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [GradedDehomogenization.map_homogeneous G hb n _ (decompose G x n).property,
    toQuotient_mk G hb]

theorem map_variable : GradedDehomogenization.map G hb b = 1 := by
  rw [GradedDehomogenization.map_homogeneous G hb 1 b hb]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, val_one, pow_one, Localization.mk_eq_mk']
  exact IsLocalization.mk'_self (Localization.Away b)
    (show b ∈ Submonoid.powers b from ⟨1, pow_one b⟩)

theorem map_kernel : RingHom.ker (GradedDehomogenization.map G hb) = ideal b := by
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (ideal b) x = 0
    rw [← toQuotient_comp G hb]
    change toQuotient G (GradedDehomogenization.map G hb x) = 0
    rw [RingHom.mem_ker.mp hx, map_zero]
  · rw [ideal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp only [map_sub, map_one, map_variable G hb, sub_self]

def equiv : A ⧸ ideal b ≃+* Away G b :=
  (Ideal.quotEquivOfEq (map_kernel G hb).symm).trans
    ((GradedDehomogenization.map G hb).quotientKerEquivOfSurjective
      (GradedDehomogenization.map_surjective G hb))

theorem equiv_mk (x : A) : equiv G hb (Ideal.Quotient.mk (ideal b) x) =
    GradedDehomogenization.map G hb x := by
  rw [equiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end PaperP1.GradedDehomogenizationQuotient
