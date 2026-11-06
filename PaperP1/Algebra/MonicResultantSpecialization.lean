module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.CharP.Basic

/-! # Literal common-root specialization, monic fibre bounds and nonzero derivative resultants -/

set_option autoImplicit false

@[expose] public noncomputable section
namespace PaperP1.MonicResultantSpecialization
open Polynomial Finset
open scoped Classical

section Specialization
variable {R F : Type*} [CommRing R] [Field F]

theorem common_base_zero (P Q : R[X]) (hpos : 0 < P.natDegree) (φ : R →+* F) (z : F)
    (hP : P.eval₂ φ z = 0) (hQ : Q.eval₂ φ z = 0) : φ (P.resultant Q) = 0 := by
  obtain ⟨a, b, _ha, _hb, he⟩ := exists_mul_add_mul_eq_C_resultant P Q le_rfl le_rfl
    (Or.inl (ne_of_gt hpos))
  have hh := congrArg (fun T : R[X] ↦ T.eval₂ φ z) he
  simp only [eval₂_add, eval₂_mul, hP, hQ, zero_mul, zero_add, eval₂_C] at hh
  exact hh.symm

theorem monic_fibre_card (P : R[X]) (hP : P.Monic) (φ : R →+* F) (S : Finset F)
    (hS : ∀ z ∈ S, P.eval₂ φ z = 0) : S.card ≤ P.natDegree := by
  have hb : S.card ≤ (P.map φ).natDegree := by
    apply card_le_degree_of_subset_roots
    intro z hz
    apply (mem_roots (hP.map φ).ne_zero).mpr
    change (P.map φ).eval z = 0
    rw [eval_map]
    exact hS z hz
  exact hb.trans natDegree_map_le
end Specialization

section Nonzero
variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]

theorem resultant_nonzero_of_not_dvd (P Q : R[X]) (hmonic : P.Monic)
    (hP : Irreducible P) (hnot : ¬P ∣ Q) : P.resultant Q ≠ 0 := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hinj : Function.Injective φ := IsFractionRing.injective R K
  have hirr : Irreducible (P.map φ) :=
    (hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hnd : ¬P.map φ ∣ Q.map φ := by
    intro hd
    exact hnot ((hmonic.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map K).mpr hd)
  have hn := Polynomial.resultant_ne_zero (P.map φ) (Q.map φ) (hirr.coprime_iff_not_dvd.mpr hnd)
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj] at hn
  intro hz
  apply hn
  rw [Polynomial.resultant_map_map, hz, map_zero]
end Nonzero

section Characteristic
variable {R : Type*} [CommRing R] (p : ℕ) [CharP R p]

theorem monic_derivative_ne_zero (P : R[X]) (hmonic : P.Monic)
    (hpos : 0 < P.natDegree) (hlt : P.natDegree < p) : P.derivative ≠ 0 := by
  intro hz
  have hc := congrArg (fun Q : R[X] ↦ Q.coeff (P.natDegree-1)) hz
  have hs : P.natDegree-1+1 = P.natDegree := Nat.sub_add_cancel hpos
  simp only [coeff_derivative, hs, hmonic.coeff_natDegree, one_mul, coeff_zero] at hc
  have hc' : ((P.natDegree-1+1 : ℕ) : R) = 0 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hc
  rw [hs] at hc'
  have hd : p ∣ P.natDegree := (CharP.cast_eq_zero_iff R p _).mp hc'
  exact (Nat.not_le_of_lt hlt) (Nat.le_of_dvd hpos hd)

variable [IsDomain R] [IsGCDMonoid R]
theorem derivative_resultant_nonzero (P : R[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hpos : 0 < P.natDegree) (hlt : P.natDegree < p) : P.resultant P.derivative ≠ 0 := by
  apply resultant_nonzero_of_not_dvd P P.derivative hmonic hP
  intro hd
  have hne := monic_derivative_ne_zero p P hmonic hpos hlt
  exact (not_lt_of_ge (natDegree_le_of_dvd hd hne)) (natDegree_derivative_lt (ne_of_gt hpos))
end Characteristic
end PaperP1.MonicResultantSpecialization
