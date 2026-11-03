module

public import PaperP1.Algebra.RationalGraphFieldTower
public import Mathlib.Algebra.Polynomial.Degree.Units

/-! # Explicit reduced rational graphs from two common-quotient fibre equations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonQuotientGraph

open Polynomial

variable {F : Type*} [Field F]

def denominator (A B : F[X]) : F[X] := A - B

def numerator (A B : F[X]) (j₀ j₁ : F) : F[X] := C j₀ * B - C j₁ * A

theorem first_identity (A B : F[X]) (j₀ j₁ : F) :
    numerator A B j₀ j₁ + C j₀ * denominator A B = C (j₀ - j₁) * A := by
  simp only [numerator, denominator, map_sub]
  ring

theorem second_identity (A B : F[X]) (j₀ j₁ : F) :
    numerator A B j₀ j₁ + C j₁ * denominator A B = C (j₀ - j₁) * B := by
  simp only [numerator, denominator, map_sub]
  ring

theorem denominator_ne_zero (A B : F[X]) (hcop : IsCoprime A B) (hA : 0 < A.natDegree) :
    denominator A B ≠ 0 := by
  intro hz
  have hAB : A = B := sub_eq_zero.mp hz
  have hu : IsUnit A := isCoprime_self.mp (by simpa only [← hAB] using hcop)
  exact not_isUnit_of_natDegree_pos A hA hu

theorem coprime (A B : F[X]) (j₀ j₁ : F) (hne : j₀ ≠ j₁) (hcop : IsCoprime A B) :
    IsCoprime (numerator A B j₀ j₁) (denominator A B) := by
  have hqB : IsCoprime (denominator A B) B := by
    simpa only [denominator, one_mul] using
      (IsCoprime.sub_mul_right_left_iff (x := A) (y := B) (z := 1)).mpr hcop
  have hu : IsUnit (C (j₀ - j₁) : F[X]) := (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map C
  have hBq : IsCoprime (C (j₀ - j₁) * B) (denominator A B) :=
    (isCoprime_mul_unit_left_left hu _ _).mpr hqB.symm
  have hp : numerator A B j₀ j₁ = C (j₀ - j₁) * B - C j₁ * denominator A B := by
    linear_combination second_identity A B j₀ j₁
  rw [hp]
  exact IsCoprime.sub_mul_right_left_iff.mpr hBq

theorem exact_degree (A B : F[X]) (j₀ j₁ : F) (hne : j₀ ≠ j₁) (a : ℕ)
    (hA : A.natDegree = a) (hB : B.natDegree = a) :
    max (numerator A B j₀ j₁).natDegree (denominator A B).natDegree = a := by
  have hq : (denominator A B).natDegree ≤ a :=
    (natDegree_sub_le A B).trans (max_le hA.le hB.le)
  have hp : (numerator A B j₀ j₁).natDegree ≤ a :=
    (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le j₀ B).trans hB.le)
      ((natDegree_C_mul_le j₁ A).trans hA.le))
  apply le_antisymm (max_le hp hq)
  have h := natDegree_add_le (numerator A B j₀ j₁) (C j₀ * denominator A B)
  rw [first_identity, natDegree_C_mul (sub_ne_zero.mpr hne), hA] at h
  exact h.trans (max_le_max le_rfl (natDegree_C_mul_le j₀ (denominator A B)))

theorem denominator_nonvanishing (p q : F[X]) (hcop : IsCoprime p q) (z v : F)
    (hpoint : p.eval z = v * q.eval z) : q.eval z ≠ 0 := by
  intro hz
  have hp : p.eval z = 0 := hpoint.trans (by rw [hz, mul_zero])
  have h := Polynomial.aeval_ne_zero_of_isCoprime hcop z
  simp only [coe_aeval_eq_eval, hp, hz, ne_eq, not_true_eq_false, or_self] at h

variable {E : Type*} [Field E] [Algebra F E]

theorem distinct_constants (x y t : E) (hx : Transcendental F x) (A B : F[X])
    (j₀ j₁ : F) (hcop : IsCoprime A B) (hA : 0 < A.natDegree)
    (hfirst : aeval x A = t * (y + algebraMap F E j₀))
    (hsecond : aeval x B = t * (y + algebraMap F E j₁)) : j₀ ≠ j₁ := by
  intro heq
  have hAB : A = B := transcendental_iff_injective.mp hx (hfirst.trans (by rw [heq, ← hsecond]))
  exact denominator_ne_zero A B hcop hA (by simp only [denominator, hAB, sub_self])

theorem denominator_evaluation (x y t : E) (A B : F[X]) (j₀ j₁ : F)
    (hfirst : aeval x A = t * (y + algebraMap F E j₀))
    (hsecond : aeval x B = t * (y + algebraMap F E j₁)) :
    aeval x (denominator A B) = t * algebraMap F E (j₀ - j₁) := by
  simp only [denominator, map_sub, hfirst, hsecond]
  ring

theorem graph_evaluation (x y t : E) (A B : F[X]) (j₀ j₁ : F)
    (hfirst : aeval x A = t * (y + algebraMap F E j₀))
    (hsecond : aeval x B = t * (y + algebraMap F E j₁)) :
    aeval x (numerator A B j₀ j₁) = y * aeval x (denominator A B) := by
  simp only [numerator, denominator, map_sub, map_mul, aeval_C, hfirst, hsecond]
  ring

theorem fibre_identity (x y t : E) (hx : Transcendental F x) (A B P : F[X]) (j₀ j₁ j : F)
    (hfirst : aeval x A = t * (y + algebraMap F E j₀))
    (hsecond : aeval x B = t * (y + algebraMap F E j₁))
    (hthird : aeval x P = t * (y + algebraMap F E j)) :
    numerator A B j₀ j₁ + C j * denominator A B = C (j₀ - j₁) * P := by
  apply transcendental_iff_injective.mp hx
  simp only [map_add, map_mul, aeval_C, map_sub]
  rw [graph_evaluation x y t A B j₀ j₁ hfirst hsecond,
    denominator_evaluation x y t A B j₀ j₁ hfirst hsecond, hthird, map_sub]
  ring

theorem root_match (x y t : E) (hx : Transcendental F x) (A B P : F[X]) (j₀ j₁ j z : F)
    (hfirst : aeval x A = t * (y + algebraMap F E j₀))
    (hsecond : aeval x B = t * (y + algebraMap F E j₁))
    (hthird : aeval x P = t * (y + algebraMap F E j)) (hz : P.eval z = 0) :
    (numerator A B j₀ j₁).eval z = -j * (denominator A B).eval z := by
  have h := congrArg (fun p : F[X] ↦ p.eval z) (fibre_identity x y t hx A B P j₀ j₁ j hfirst hsecond hthird)
  simp only [eval_add, eval_mul, eval_C, hz, mul_zero] at h
  linear_combination h

end PaperP1.CommonQuotientGraph
