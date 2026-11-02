module

public import PaperP1.Arithmetic.IntegerCurvePointInput
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # The actual integer-to-rational polynomial bridge for the conditional BCN input -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerCurveRationalization

open Polynomial PaperP1.PlaneCurvePointCount PaperP1.BivariateTotalDegree

attribute [local instance] Polynomial.algebra

def coefficientMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : R[X][X] →+* S[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom f)

theorem coefficientMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) : Function.Injective (coefficientMap f) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ hf)

theorem degree_coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (P : R[X][X]) :
    PlaneCurvePointCount.degree (coefficientMap f P) = PlaneCurvePointCount.degree P := by
  unfold PlaneCurvePointCount.degree coefficientMap
  simp only [coe_mapRingHom]
  rw [support_map_of_injective P (Polynomial.map_injective _ hf)]
  apply Finset.sup_congr rfl
  intro i _hi
  simp only [coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective hf]

theorem degree_of_isUnit {R : Type*} [CommRing R] [IsDomain R] (P : R[X][X]) (hP : IsUnit P) :
    PlaneCurvePointCount.degree P = 0 := by
  obtain ⟨p, hp, rfl⟩ := Polynomial.isUnit_iff.mp hP
  obtain ⟨a, _ha, rfl⟩ := Polynomial.isUnit_iff.mp hp
  apply Nat.le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  have hnz := mem_support_iff.mp hi
  have hi0 : i = 0 := by
    by_contra hne
    exact hnz (by rw [coeff_C]; simp only [hne, ite_false])
  subst i
  simpa only [coeff_C_zero, natDegree_C, zero_add] using (le_refl (0 : ℕ))

theorem grid_coefficientMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (P : R[X][X]) (B : ℕ) :
    grid (coefficientMap f P) B = grid P B := by
  classical
  ext p
  simp only [mem_grid]
  have he : (coefficientMap f P).evalEval (p.1 : S) (p.2 : S) =
      f (P.evalEval (p.1 : R) (p.2 : R)) := by
    simpa only [coefficientMap, coe_mapRingHom, map_intCast] using
      Polynomial.map_mapRingHom_evalEval f P (p.1 : R) (p.2 : R)
  rw [he, ← f.map_zero, hf.eq_iff]

theorem rational_irreducible (P : ℤ[X][X]) (hP : Irreducible P) (hD : 0 < totalDegree P) :
    Irreducible (coefficientMap (Int.castRingHom ℚ) P) := by
  let S : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map Polynomial.C
  let : IsLocalization S ℚ[X] := Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  let : IsLocalization (S.map Polynomial.C) ℚ[X][X] := Polynomial.isLocalization S ℚ[X]
  let f := IsLocalization.toLocalizationMap (S.map Polynomial.C) ℚ[X][X]
  have hinj : Function.Injective (coefficientMap (Int.castRingHom ℚ)) :=
    coefficientMap_injective _ (Int.cast_injective (α := ℚ))
  have hdeg : 0 < PlaneCurvePointCount.degree (coefficientMap (Int.castRingHom ℚ) P) := by
    rw [degree_coefficientMap _ (Int.cast_injective (α := ℚ))]
    exact hD
  have hnz : coefficientMap (Int.castRingHom ℚ) P ≠ 0 := by
    intro h
    exact hP.ne_zero (hinj (h.trans (map_zero _).symm))
  have hnu : ¬ IsUnit (coefficientMap (Int.castRingHom ℚ) P) := by
    intro hu
    have hz := degree_of_isUnit _ hu
    omega
  change Irreducible (f P)
  exact (f.map_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hP) hnz hnu).irreducible

theorem integer_input_of_field_input (c κ : ℝ) (hBCN : PlaneCurvePointCount.UniformBound c κ) :
    IntegerCurvePointInput.UniformBound c κ := by
  intro P hP hD H hH
  have h := hBCN ℚ (coefficientMap (Int.castRingHom ℚ) P) (rational_irreducible P hP hD)
    (by rw [degree_coefficientMap _ (Int.cast_injective (α := ℚ))]; exact hD) H hH
  rw [degree_coefficientMap _ (Int.cast_injective (α := ℚ)),
    grid_coefficientMap _ (Int.cast_injective (α := ℚ))] at h
  rw [PlaneCurvePointCount.integer_grid_card]
  exact h

end PaperP1.IntegerCurveRationalization
