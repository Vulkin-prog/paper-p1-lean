module

public import PaperP1.Algebra.IntegerPlaneShear
public import Mathlib.Algebra.Polynomial.Roots

/-! # A bounded integer shear makes the outer degree equal the total degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedPlaneShear

open Polynomial Finset PaperP1.TotalDegreeMonomials PaperP1.BivariateLinearShear

def direction (D : ℕ) (P : ℤ[X][X]) : ℤ[X] :=
  ∑ i : Index D, if i.val.1.val + i.val.2.val = D then
    Polynomial.monomial i.val.1.val ((P.coeff i.val.2.val).coeff i.val.1.val) else 0

theorem direction_coefficient (D : ℕ) (P : ℤ[X][X]) (j : Index D)
    (hj : j.val.1.val + j.val.2.val = D) :
    (direction D P).coeff j.val.1.val = (P.coeff j.val.2.val).coeff j.val.1.val := by
  classical
  simp only [direction, Polynomial.finsetSum_coeff]
  have he (i : Index D) :
      (if i.val.1.val + i.val.2.val = D then
        Polynomial.monomial i.val.1.val ((P.coeff i.val.2.val).coeff i.val.1.val) else 0).coeff j.val.1.val =
      if i = j then (P.coeff j.val.2.val).coeff j.val.1.val else 0 := by
    by_cases hij : i = j
    · subst i
      simp [hj]
    by_cases ht : i.val.1.val + i.val.2.val = D
    · have hx : i.val.1.val ≠ j.val.1.val := by
        intro heq
        have hy : i.val.2.val = j.val.2.val := by omega
        exact hij (Subtype.ext (Prod.ext (Fin.ext heq) (Fin.ext hy)))
      simp [ht, Polynomial.coeff_monomial, hx, hij]
    · simp [ht, hij]
  simp_rw [he]
  simp

theorem direction_degree (D : ℕ) (P : ℤ[X][X]) : (direction D P).natDegree ≤ D := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _hi
  by_cases ht : i.val.1.val + i.val.2.val = D
  · simp only [ite_true, ht]
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  · simp [ht]

theorem direction_ne_zero (P : ℤ[X][X]) (hP : P ≠ 0) :
    direction (PlaneCurvePointCount.degree P) P ≠ 0 := by
  classical
  have hs : P.support.Nonempty := Polynomial.support_nonempty.mpr hP
  obtain ⟨y, hy, hmax⟩ := Finset.exists_mem_eq_sup P.support hs (fun y ↦ y + (P.coeff y).natDegree)
  have hrow : P.coeff y ≠ 0 := Polynomial.mem_support_iff.mp hy
  let x := (P.coeff y).natDegree
  have hxy : x + y = PlaneCurvePointCount.degree P := by
    change PlaneCurvePointCount.degree P = y + (P.coeff y).natDegree at hmax
    dsimp only [x]
    omega
  let j : Index (PlaneCurvePointCount.degree P) :=
    ⟨(⟨x, by omega⟩, ⟨y, by omega⟩), hxy.le⟩
  have hc : (P.coeff y).coeff x ≠ 0 := by
    dsimp only [x]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hrow
  intro hz
  have he := direction_coefficient (PlaneCurvePointCount.degree P) P j hxy
  rw [hz, Polynomial.coeff_zero] at he
  exact hc he.symm

theorem exists_bounded_nonroot (D : ℕ) (q : ℤ[X]) (hq : q ≠ 0) (hdeg : q.natDegree ≤ D) :
    ∃ t : ℕ, t ≤ D ∧ q.eval (t : ℤ) ≠ 0 := by
  classical
  by_contra hn
  have hz : ∀ t : ℕ, t ≤ D → q.eval (t : ℤ) = 0 := by
    intro t ht
    by_contra hne
    exact hn ⟨t, ht, hne⟩
  let S : Finset ℤ := (range (D + 1)).image (fun t : ℕ ↦ (t : ℤ))
  have hsub : S.val ⊆ q.roots := by
    intro z hzS
    have hz' : z ∈ S := hzS
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hz'
    exact (Polynomial.mem_roots hq).mpr (hz t (by have hh := mem_range.mp ht; omega))
  have hc := Polynomial.card_le_degree_of_subset_roots hsub
  have hcard : S.card = D + 1 := by
    rw [card_image_of_injective _ Nat.cast_injective, card_range]
  omega

theorem exists_direction_nonzero (P : ℤ[X][X]) (hP : P ≠ 0) :
    ∃ t : ℕ, t ≤ PlaneCurvePointCount.degree P ∧
      (direction (PlaneCurvePointCount.degree P) P).eval (t : ℤ) ≠ 0 :=
  exists_bounded_nonroot _ _ (direction_ne_zero P hP) (direction_degree _ P)

def diagonal (t : ℤ) : ℤ[X][X] →+* ℤ[X] :=
  (Polynomial.mapRingHom (Polynomial.evalRingHom 0)).comp (shear t).toRingHom

theorem diagonal_monomial (t c : ℤ) (x y : ℕ) :
    diagonal t (Polynomial.monomial y (Polynomial.monomial x c)) =
      Polynomial.monomial (x + y) (c * t ^ x) := by
  have hm : Polynomial.monomial y (Polynomial.monomial x c) = C (C c) * C X ^ x * X ^ y := by
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
  rw [hm, ← Polynomial.C_mul_X_pow_eq_monomial]
  let E : ℤ[X][X] →+* ℤ[X] := Polynomial.mapRingHom (Polynomial.evalRingHom 0)
  have hE (a : ℤ) : E (C (C a)) = C a := by simp [E]
  have hEx : E (C X) = 0 := by simp [E]
  have hEy : E X = X := by simp [E]
  change E (shear t (C (C c) * C X ^ x * X ^ y)) = _
  simp only [map_mul, map_pow, IntegerPlaneShear.scalar, IntegerPlaneShear.inner_variable,
    IntegerPlaneShear.outer_variable, map_add, hE, hEx, hEy, zero_add, mul_pow, pow_add]
  ring

theorem diagonal_coefficient (D : ℕ) (t : ℤ) (P : ℤ[X][X])
    (hD : PlaneCurvePointCount.degree P ≤ D) :
    (diagonal t P).coeff D = (direction D P).eval t := by
  classical
  have hrec := TotalDegreeMonomials.reconstruction D P hD
  conv_lhs => rw [← hrec]
  rw [TotalDegreeMonomials.polynomial, map_sum, Polynomial.finsetSum_coeff,
    direction, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [diagonal_monomial]
  by_cases ht : i.val.1.val + i.val.2.val = D
  · simp [ht]
  · simp [ht, Polynomial.coeff_monomial]

theorem exists_full_outer_degree (P : ℤ[X][X]) (hP : P ≠ 0) :
    ∃ t : ℕ, t ≤ PlaneCurvePointCount.degree P ∧
      (shear (t : ℤ) P).natDegree = PlaneCurvePointCount.degree P := by
  obtain ⟨t, ht, hnonzero⟩ := exists_direction_nonzero P hP
  refine ⟨t, ht, ?_⟩
  have hc : (diagonal (t : ℤ) P).coeff (PlaneCurvePointCount.degree P) ≠ 0 := by
    rw [diagonal_coefficient _ _ _ le_rfl]
    exact hnonzero
  have hcoeff : (shear (t : ℤ) P).coeff (PlaneCurvePointCount.degree P) ≠ 0 := by
    intro hz
    apply hc
    change (((shear (t : ℤ) P).map (Polynomial.evalRingHom 0)).coeff _) = 0
    rw [Polynomial.coeff_map, hz, map_zero]
  apply le_antisymm
  · exact (BivariateResultantDegree.outer_degree_le _).trans_eq (shear_degree _ P)
  · exact Polynomial.le_natDegree_of_ne_zero hcoeff

end PaperP1.BoundedPlaneShear
