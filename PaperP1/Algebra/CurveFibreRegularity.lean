module

public import PaperP1.Algebra.CurveCriticalFibres
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Full degree, separability and actual root counts outside the critical fibres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveFibreRegularity

open Polynomial PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres

def coefficientSpecialization {K : Type*} [Field K] (u : ℤ) : ℤ[X] →+* K :=
  (Int.castRingHom K).comp (Polynomial.evalRingHom (-u))

def fibre {K : Type*} [Field K] (P : ℤ[X][X]) (u : ℤ) : K[X] :=
  P.map (coefficientSpecialization u)

theorem fibre_degree {K : Type*} [Field K] [CharZero K] (P : ℤ[X][X])
    (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P) :
    (fibre (K := K) P u).natDegree = degreeY P := by
  have hl := ((regular_iff P hP hy u).mp hu).1
  have hmap : coefficientSpecialization (K := K) u P.leadingCoeff ≠ 0 := by
    change ((P.leadingCoeff.eval (-u) : ℤ) : K) ≠ 0
    exact_mod_cast hl
  exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hmap

theorem fibre_nonzero {K : Type*} [Field K] [CharZero K] (P : ℤ[X][X])
    (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P) :
    fibre (K := K) P u ≠ 0 := by
  intro hz
  have h := fibre_degree (K := K) P hP hy u hu
  rw [hz, natDegree_zero] at h
  omega

theorem fibre_separable {K : Type*} [Field K] [CharZero K] (P : ℤ[X][X])
    (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P) :
    (fibre (K := K) P u).Separable := by
  let φ : ℤ[X] →+* K := coefficientSpecialization u
  have hm : (P.map φ).natDegree = P.natDegree := fibre_degree (K := K) P hP hy u hu
  have hdm : (P.derivative.map φ).natDegree = P.derivative.natDegree := by
    rw [← Polynomial.derivative_map, Polynomial.natDegree_derivative, hm, Polynomial.natDegree_derivative]
  have hr := ((regular_iff P hP hy u).mp hu).2
  have hrmap : φ (P.resultant P.derivative) ≠ 0 := by
    change (((P.resultant P.derivative).eval (-u) : ℤ) : K) ≠ 0
    exact_mod_cast hr
  have hres : (fibre (K := K) P u).resultant (fibre (K := K) P u).derivative ≠ 0 := by
    intro hz
    apply hrmap
    rw [← Polynomial.resultant_map_map]
    change (P.map φ).resultant (P.map φ).derivative = 0 at hz
    rw [Polynomial.derivative_map, hm, hdm] at hz
    exact hz
  rw [Polynomial.separable_def]
  by_contra hn
  exact hres (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl (fibre_nonzero (K := K) P hP hy u hu), hn⟩)

theorem root_derivative_ne_zero {K : Type*} [Field K] [CharZero K] (P : ℤ[X][X])
    (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P)
    (z : K) (hz : (fibre P u).eval z = 0) : (fibre P u).derivative.eval z ≠ 0 := by
  obtain ⟨A, B, hbez⟩ := (Polynomial.separable_def' _).mp (fibre_separable (K := K) P hP hy u hu)
  intro hd
  have h := congrArg (Polynomial.evalRingHom z) hbez
  simp only [map_add, map_mul, map_one, coe_evalRingHom, hz, hd, mul_zero, zero_add] at h
  exact zero_ne_one h

theorem fibre_roots_card {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K] (P : ℤ[X][X])
    (hP : Irreducible P) (hy : 0 < degreeY P) (u : ℤ) (hu : u ∉ badOffsets P) :
    (fibre (K := K) P u).roots.toFinset.card = degreeY P := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (fibre_separable (K := K) P hP hy u hu))]
  exact (IsAlgClosed.splits (fibre (K := K) P u)).natDegree_eq_card_roots.symm.trans
    (fibre_degree (K := K) P hP hy u hu)

theorem fibre_integer_evaluation {K : Type*} [Field K] (P : ℤ[X][X]) (u v : ℤ) :
    (fibre (K := K) P u).eval (-(v : K)) = ((P.evalEval (-u) (-v) : ℤ) : K) := by
  have he : (Polynomial.evalRingHom (-(v : K))).comp (Polynomial.mapRingHom (coefficientSpecialization u)) =
      (Int.castRingHom K).comp (Polynomial.evalEvalRingHom (-u) (-v)) := by
    ext <;> simp [coefficientSpecialization]
  exact congrArg (fun φ : ℤ[X][X] →+* K ↦ φ P) he

end PaperP1.CurveFibreRegularity
