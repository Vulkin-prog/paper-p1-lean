module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Lean.Elab.Tactic.Omega

/-! # Boundedly many actual irreducible components of a bounded bivariate polynomial

The sum of the two partial degrees is additive on nonzero products and positive
on nonunits. It bounds both the number and the degrees of irreducible factors.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateFactorDegree

open Polynomial UniqueFactorizationMonoid

variable {K : Type*} [Field K]

def degreeSum (P : K[X][X]) : ℕ := (Bivariate.swap P).natDegree + P.natDegree

def totalDegree (P : K[X][X]) : ℕ := P.support.sup (fun j ↦ j + (P.coeff j).natDegree)

theorem coeff_swap (P : K[X][X]) (i j : ℕ) :
    ((Bivariate.swap P).coeff j).coeff i = (P.coeff i).coeff j := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      by_cases hn : n = i <;> by_cases hm : m = j <;> simp [coeff_monomial, hn, hm]

theorem swap_degree_le (P : K[X][X]) (d : ℕ) (h : ∀ i, (P.coeff i).natDegree ≤ d) :
    (Bivariate.swap P).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext i
  rw [coeff_swap, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt ((h i).trans_lt hn)

theorem coefficient_degree_le (P : K[X][X]) (i j : ℕ) (hc : (P.coeff j).coeff i ≠ 0) :
    i + j ≤ totalDegree P := by
  have hj : P.coeff j ≠ 0 := fun h ↦ hc (by rw [h, coeff_zero])
  have hi := le_natDegree_of_ne_zero hc
  have hs := Finset.le_sup (f := fun n ↦ n + (P.coeff n).natDegree) (mem_support_iff.mpr hj)
  unfold totalDegree
  omega

theorem totalDegree_le_degreeSum (P : K[X][X]) : totalDegree P ≤ degreeSum P := by
  apply Finset.sup_le
  intro j hj
  have hrow : P.coeff j ≠ 0 := mem_support_iff.mp hj
  have hc : (P.coeff j).coeff (P.coeff j).natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hrow
  have hs : (Bivariate.swap P).coeff (P.coeff j).natDegree ≠ 0 := by
    intro hzero
    apply hc
    rw [← coeff_swap, hzero, coeff_zero]
  have hin := le_natDegree_of_ne_zero hs
  have hout := le_natDegree_of_ne_zero hrow
  unfold degreeSum
  omega

theorem partial_degrees_le_total (P : K[X][X]) :
    P.natDegree ≤ totalDegree P ∧ (Bivariate.swap P).natDegree ≤ totalDegree P := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i
    rw [coeff_zero]
    by_contra hc
    have hh := coefficient_degree_le P i j hc
    omega
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    ext j
    rw [coeff_swap, coeff_zero]
    by_contra hc
    have hh := coefficient_degree_le P i j hc
    omega

theorem rectangle_bound (P : K[X][X]) (d : ℕ) (hy : P.natDegree ≤ d)
    (hx : ∀ i, (P.coeff i).natDegree ≤ d) : degreeSum P ≤ 2 * d := by
  unfold degreeSum
  have hs := swap_degree_le P d hx
  omega

theorem mul_degree (P Q : K[X][X]) (hp : P ≠ 0) (hq : Q ≠ 0) :
    degreeSum (P * Q) = degreeSum P + degreeSum Q := by
  have hsp : Bivariate.swap P ≠ 0 := by
    intro h
    apply hp
    apply (Bivariate.swap (R := K)).injective
    rw [h, map_zero]
  have hsq : Bivariate.swap Q ≠ 0 := by
    intro h
    apply hq
    apply (Bivariate.swap (R := K)).injective
    rw [h, map_zero]
  simp only [degreeSum, map_mul, natDegree_mul hp hq, natDegree_mul hsp hsq]
  omega

theorem unit_degree (P : K[X][X]) (hp : IsUnit P) : degreeSum P = 0 := by
  have hs : IsUnit (Bivariate.swap P) := hp.map (Bivariate.swap (R := K)).toRingHom
  simp only [degreeSum, natDegree_eq_zero_of_isUnit hp, natDegree_eq_zero_of_isUnit hs, zero_add]

theorem associated_degree (P Q : K[X][X]) (hp : P ≠ 0) (h : Associated P Q) :
    degreeSum P = degreeSum Q := by
  obtain ⟨u, hu⟩ := h
  rw [← hu, mul_degree P (u : K[X][X]) hp u.ne_zero, unit_degree _ u.isUnit, add_zero]

theorem eq_constant_of_degree_zero (P : K[X][X]) (h : degreeSum P = 0) :
    P = C (C ((P.coeff 0).coeff 0)) := by
  have hout : P.natDegree = 0 := by unfold degreeSum at h; omega
  have hs : (Bivariate.swap P).natDegree = 0 := by unfold degreeSum at h; omega
  have he := eq_C_of_natDegree_eq_zero hout
  rw [he, Bivariate.swap_C, natDegree_map_eq_of_injective C_injective] at hs
  exact he.trans (congrArg C (eq_C_of_natDegree_eq_zero hs))

theorem irreducible_degree_pos (P : K[X][X]) (hp : Irreducible P) : 0 < degreeSum P := by
  by_contra h
  have he := eq_constant_of_degree_zero P (by omega)
  have hc : (P.coeff 0).coeff 0 ≠ 0 := by
    intro hz
    apply hp.ne_zero
    rw [he, hz, C_0, C_0]
  apply hp.not_isUnit
  rw [he, isUnit_C, isUnit_C]
  exact isUnit_iff_ne_zero.mpr hc

theorem irreducible_totalDegree_pos (P : K[X][X]) (hp : Irreducible P) : 0 < totalDegree P := by
  have hpartial := partial_degrees_le_total P
  have hsum := irreducible_degree_pos P hp
  unfold degreeSum at hsum
  omega

theorem multiset_bounds (F : Multiset K[X][X]) (hf : ∀ P ∈ F, Irreducible P) :
    F.prod ≠ 0 ∧ F.card ≤ degreeSum F.prod ∧ ∀ P ∈ F, degreeSum P ≤ degreeSum F.prod := by
  induction F using Multiset.induction_on with
  | empty => simp [degreeSum]
  | @cons P F ih =>
    have hp : Irreducible P := hf P (Multiset.mem_cons_self _ _)
    have htail : ∀ Q ∈ F, Irreducible Q := fun Q hQ ↦ hf Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hne, hcard, hdegrees⟩ := ih htail
    have hpos := irreducible_degree_pos P hp
    rw [Multiset.prod_cons, Multiset.card_cons, mul_degree P F.prod hp.ne_zero hne]
    refine ⟨mul_ne_zero hp.ne_zero hne, by omega, ?_⟩
    intro Q hQ
    rcases Multiset.mem_cons.mp hQ with rfl | hQ
    · omega
    · have hh := hdegrees Q hQ; omega

variable [NormalizationMonoid K[X][X]]

theorem normalized_factor_bounds (P : K[X][X]) (hp : P ≠ 0) :
    (normalizedFactors P).card ≤ degreeSum P ∧
      ∀ Q ∈ normalizedFactors P, Irreducible Q ∧ degreeSum Q ≤ degreeSum P := by
  have hirr : ∀ Q ∈ normalizedFactors P, Irreducible Q :=
    UniqueFactorizationMonoid.irreducible_of_normalized_factor
  obtain ⟨hne, hcard, hdegree⟩ := multiset_bounds (normalizedFactors P) hirr
  have he := associated_degree _ P hne (UniqueFactorizationMonoid.prod_normalizedFactors hp)
  rw [he] at hcard hdegree
  exact ⟨hcard, fun Q hQ ↦ ⟨hirr Q hQ, hdegree Q hQ⟩⟩

theorem zero_on_factor (P : K[X][X]) (hp : P ≠ 0) (x y : K) (hz : P.evalEval x y = 0) :
    ∃ Q ∈ normalizedFactors P, Q.evalEval x y = 0 := by
  obtain ⟨u, hu⟩ := prod_normalizedFactors hp
  have he := congrArg (evalEvalRingHom x y) hu
  rw [map_mul] at he
  have hunit : (evalEvalRingHom x y) (u : K[X][X]) ≠ 0 :=
    (u.isUnit.map (evalEvalRingHom x y)).ne_zero
  have hzprod : ((normalizedFactors P).prod).evalEval x y = 0 :=
    (mul_eq_zero.mp (he.trans hz)).resolve_right hunit
  rw [evalEval_multiset_prod] at hzprod
  obtain ⟨Q, hQ, heval⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hzprod)
  exact ⟨Q, hQ, heval⟩

end PaperP1.BivariateFactorDegree
