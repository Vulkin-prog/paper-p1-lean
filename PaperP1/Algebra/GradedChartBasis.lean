module

public import PaperP1.Algebra.GradedDehomogenizationQuotient
public import PaperP1.Algebra.QuotientFreeBasis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Transporting an actual free graded ring basis to degree-one affine charts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedChartBasis

open HomogeneousLocalization Module GradedDehomogenizationQuotient

variable {A B σ τ ι : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  (G : ℕ → σ) {H : ℕ → τ} [GradedRing G] [GradedRing H]
  {b : A} (hb : b ∈ G 1) (f : G →+*ᵍ H)

def targetEquiv :
    letI : Algebra A B := f.toRingHom.toAlgebra
    B ⧸ (ideal b).map (algebraMap A B) ≃+* Away H (f b) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  have hI : (ideal b).map (algebraMap A B) = ideal (f b) := by
    simp only [ideal, Ideal.map_span, Set.image_singleton, map_sub, map_one]
    rfl
  exact (Ideal.quotEquivOfEq hI).trans (equiv H (f.map_mem hb))

omit [AddSubgroupClass σ A] [GradedRing G] in
theorem targetEquiv_mk (x : B) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    targetEquiv G hb f (Ideal.Quotient.mk _ x) = GradedDehomogenization.map H (f.map_mem hb) x := by
  let : Algebra A B := f.toRingHom.toAlgebra
  rw [targetEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, equiv_mk]

theorem targetEquiv_commutes (a : A) :
    letI : Algebra A B := f.toRingHom.toAlgebra
    targetEquiv G hb f (Ideal.Quotient.mk _ (algebraMap A B a)) =
      Away.map f b (equiv G hb (Ideal.Quotient.mk _ a)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  rw [targetEquiv_mk, equiv_mk]
  exact (DFunLike.congr_fun (GradedDehomogenization.map_natural G hb f) a).symm

def basis (e : letI : Algebra A B := f.toRingHom.toAlgebra; Basis ι A B) :
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    Basis ι (Away G b) (Away H (f b)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  exact QuotientFreeBasis.transported e (ideal b) (equiv G hb) (targetEquiv G hb f)
    (Away.map f b) (targetEquiv_commutes G hb f)

set_option backward.isDefEq.respectTransparency false in
theorem basis_apply (e : letI : Algebra A B := f.toRingHom.toAlgebra; Basis ι A B) (i : ι) :
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    basis G hb f e i = GradedDehomogenization.map H (f.map_mem hb) (e i) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  rw [basis, QuotientFreeBasis.transported_apply, targetEquiv_mk]

include hb in
theorem chart_free_finite [Finite ι]
    (e : letI : Algebra A B := f.toRingHom.toAlgebra; Basis ι A B) :
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    Module.Free (Away G b) (Away H (f b)) ∧ Module.Finite (Away G b) (Away H (f b)) := by
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  exact ⟨.of_basis (basis G hb f e), .of_basis (basis G hb f e)⟩

include hb in
theorem chart_finrank [Fintype ι] [Nontrivial (Away G b)]
    (e : letI : Algebra A B := f.toRingHom.toAlgebra; Basis ι A B) :
    letI : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
    Module.finrank (Away G b) (Away H (f b)) = Fintype.card ι := by
  let : Algebra (Away G b) (Away H (f b)) := (Away.map f b).toAlgebra
  exact Module.finrank_eq_card_basis (basis G hb f e)

theorem chart_isDomain [IsDomain A] (hb0 : b ≠ 0) : IsDomain (Away G b) := by
  have : IsDomain (Localization.Away b) := IsLocalization.isDomain_localization
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hb0))
  exact (HomogeneousLocalization.val_injective (𝒜 := G) (Submonoid.powers b)).isDomain
    (algebraMap (Away G b) (Localization.Away b))

end PaperP1.GradedChartBasis
