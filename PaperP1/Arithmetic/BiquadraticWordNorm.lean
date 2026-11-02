module

public import PaperP1.Algebra.FormalWordPolynomials
public import PaperP1.Algebra.BiquadraticSourceNorm
public import PaperP1.Algebra.IntegerOverlapRoot
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # The actual integer norm polynomial of two independent reduced formal words -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticWordNorm

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.BivariateWordSquares
  PaperP1.BiquadraticSourceNorm
open scoped symmDiff

def Independent (I J K L : Finset ℤ) : Prop :=
  (I.Nonempty ∨ J.Nonempty) ∧ (K.Nonempty ∨ L.Nonempty) ∧
    ((I ∆ K).Nonempty ∨ (J ∆ L).Nonempty)

theorem independent_of_distinct (I J K L : Finset ℤ)
    (h₁ : (I, J) ≠ (∅, ∅)) (h₂ : (K, L) ≠ (∅, ∅)) (h₁₂ : (I, J) ≠ (K, L)) :
    Independent I J K L := by
  simpa only [Independent, Finset.nonempty_iff_ne_empty, ne_eq, symmDiff_eq_empty,
    Prod.mk.injEq, not_and_or] using And.intro h₁ (And.intro h₂ h₁₂)

theorem word_evaluation (I J : Finset ℤ) (x y : ℤ) :
    (wordOver ℤ I J).evalEval x y = (∏ i ∈ I, (x + i)) * ∏ j ∈ J, (y + j) := by
  simp only [wordOver, evalEval_mul, evalEval_C, evalEval_map_C, linearOver,
    eval_prod, eval_add, eval_X, eval_C, Int.cast_id]

theorem word_value_pos (I J : Finset ℤ) (x y : ℤ)
    (hx : ∀ i ∈ I, 0 < x + i) (hy : ∀ j ∈ J, 0 < y + j) :
    0 < (wordOver ℤ I J).evalEval x y := by
  rw [word_evaluation]
  exact mul_pos (prod_pos hx) (prod_pos hy)

theorem word_value_pos_of_bounds (I J : Finset ℤ) (B : ℕ) (x y : ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ)) :
    0 < (wordOver ℤ I J).evalEval x y := by
  apply word_value_pos
  · intro i hi
    have h := (abs_le.mp (hI i hi)).1
    omega
  · intro j hj
    have h := (abs_le.mp (hJ j hj)).1
    omega

theorem exists_third_root (I J K L : Finset ℤ) (x y w₁ w₂ : ℤ)
    (hg : (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y ≠ 0)
    (h₁ : w₁ ^ 2 = (wordOver ℤ I J).evalEval x y)
    (h₂ : w₂ ^ 2 = (wordOver ℤ K L).evalEval x y) :
    ∃ w₃ : ℤ, w₃ ^ 2 = (wordOver ℤ (I ∆ K) (J ∆ L)).evalEval x y ∧
      (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y * w₃ = w₁ * w₂ := by
  have hrel : (wordOver ℤ (I ∆ K) (J ∆ L)).evalEval x y *
      (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y ^ 2 =
        (wordOver ℤ I J).evalEval x y * (wordOver ℤ K L).evalEval x y := by
    simpa only [evalEval_mul, evalEval_pow] using
      congrArg (fun P : ℤ[X][X] ↦ P.evalEval x y) (word_overlap ℤ I J K L).symm
  exact IntegerOverlapRoot.exists_root _ _ _ _ w₁ w₂ hg hrel h₁ h₂

def embedding : ℤ[X][X] →+* FunctionField :=
  (algebraMap ℚ[X][X] FunctionField).comp rationalize

theorem embedding_injective : Function.Injective embedding :=
  (IsFractionRing.injective ℚ[X][X] FunctionField).comp rationalize_injective

theorem embedding_word (I J : Finset ℤ) : embedding (wordOver ℤ I J) = wordFunction I J := by
  rw [embedding, RingHom.comp_apply, rationalize_word]
  rfl

theorem wordFunction_ne_zero (I J : Finset ℤ) : wordFunction I J ≠ 0 := by
  rw [← embedding_word]
  intro h
  exact integer_word_ne_zero I J (embedding_injective (h.trans (map_zero embedding).symm))

theorem wordFunction_overlap (I J K L : Finset ℤ) :
    wordFunction I J * wordFunction K L =
      wordFunction (I ∆ K) (J ∆ L) * wordFunction (I ∩ K) (J ∩ L) ^ 2 := by
  have h := congrArg embedding (word_overlap ℤ I J K L)
  simpa only [map_mul, map_pow, embedding_word] using h

theorem product_not_square (I J K L : Finset ℤ)
    (hne : (I ∆ K).Nonempty ∨ (J ∆ L).Nonempty) :
    ¬ IsSquare (wordFunction I J * wordFunction K L) := by
  rw [wordFunction_overlap]
  intro h
  exact wordFunction_not_square _ _ hne
    ((SquareInFractionField.square_mul_square_iff _ _ (wordFunction_ne_zero _ _)).mp h)

def normPolynomial (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) : ℤ[X][X] :=
  sourceNorm (wordOver ℤ I J) (wordOver ℤ K L) (wordOver ℤ (I ∆ K) (J ∆ L))
    (wordOver ℤ (K \ I) (L \ J)) (A 0) (A 1) (A 2) (A 3)

theorem normPolynomial_ne_zero (I J K L : Finset ℤ) (hI : Independent I J K L)
    (A : Fin 4 → ℤ[X][X]) (hA : ∃ χ, A χ ≠ 0) : normPolynomial I J K L A ≠ 0 := by
  have hg : embedding (wordOver ℤ (I ∩ K) (J ∩ L)) ≠ 0 := by
    rw [embedding_word]
    exact wordFunction_ne_zero _ _
  have h₃ : embedding (wordOver ℤ (I ∆ K) (J ∆ L)) *
      embedding (wordOver ℤ (I ∩ K) (J ∩ L)) ^ 2 =
        embedding (wordOver ℤ I J) * embedding (wordOver ℤ K L) := by
    simpa only [map_mul, map_pow] using congrArg embedding (word_overlap ℤ I J K L).symm
  have hh : embedding (wordOver ℤ (K \ I) (L \ J)) *
      embedding (wordOver ℤ (I ∩ K) (J ∩ L)) = embedding (wordOver ℤ K L) := by
    have he := congrArg embedding (word_remove_overlap ℤ I J K L)
    simpa only [map_mul, mul_comm] using he
  have hne : embedding (A 0) ≠ 0 ∨ embedding (A 1) ≠ 0 ∨
      embedding (A 2) ≠ 0 ∨ embedding (A 3) ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨χ, hχ⟩ := hA
    apply hχ
    apply embedding_injective
    rw [map_zero]
    fin_cases χ <;> simp_all
  have hnorm := sourceNorm_ne_zero _ _ _ _ _ _ _ _ _ hg h₃ hh
    (by rw [embedding_word]; exact wordFunction_not_square I J hI.1)
    (by rw [embedding_word]; exact wordFunction_not_square K L hI.2.1)
    (by rw [embedding_word, embedding_word]; exact product_not_square I J K L hI.2.2) hne
  intro hzero
  apply hnorm
  rw [← map_sourceNorm]
  change embedding (normPolynomial I J K L A) = 0
  rw [hzero, map_zero]

theorem normPolynomial_evaluate_zero (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X])
    (x y w₁ w₂ w₃ : ℤ)
    (hg : (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y ≠ 0)
    (h₁ : w₁ ^ 2 = (wordOver ℤ I J).evalEval x y)
    (h₂ : w₂ ^ 2 = (wordOver ℤ K L).evalEval x y)
    (h₃ : w₃ ^ 2 = (wordOver ℤ (I ∆ K) (J ∆ L)).evalEval x y)
    (hroot : (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y * w₃ = w₁ * w₂)
    (haux : (A 0).evalEval x y + (A 1).evalEval x y * w₁ +
      (A 2).evalEval x y * w₂ + (A 3).evalEval x y * w₃ = 0) :
    (normPolynomial I J K L A).evalEval x y = 0 := by
  let φ := Polynomial.evalEvalRingHom x y
  have hh : (wordOver ℤ (I ∩ K) (J ∩ L)).evalEval x y *
      (wordOver ℤ (K \ I) (L \ J)).evalEval x y = (wordOver ℤ K L).evalEval x y := by
    simpa only [evalEval_mul] using
      congrArg (fun P : ℤ[X][X] ↦ P.evalEval x y) (word_remove_overlap ℤ I J K L)
  have hm := mixed_of_overlap _ _ _ _ _ _ hg hh h₂ hroot
  change φ (normPolynomial I J K L A) = 0
  unfold normPolynomial
  rw [map_sourceNorm]
  exact sourceNorm_zero_of_auxiliary _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ hm haux

theorem auxiliary_ne_zero {E : Type*} [CommRing E] [IsDomain E]
    (φ : ℤ[X][X] →+* E) (hφ : Function.Injective φ)
    (I J K L : Finset ℤ) (hI : Independent I J K L)
    (A : Fin 4 → ℤ[X][X]) (hA : ∃ χ, A χ ≠ 0) (w₁ w₂ w₃ : E)
    (h₁ : w₁ ^ 2 = φ (wordOver ℤ I J)) (h₂ : w₂ ^ 2 = φ (wordOver ℤ K L))
    (h₃ : w₃ ^ 2 = φ (wordOver ℤ (I ∆ K) (J ∆ L)))
    (hroot : φ (wordOver ℤ (I ∩ K) (J ∩ L)) * w₃ = w₁ * w₂) :
    φ (A 0) + φ (A 1) * w₁ + φ (A 2) * w₂ + φ (A 3) * w₃ ≠ 0 := by
  have hg : φ (wordOver ℤ (I ∩ K) (J ∩ L)) ≠ 0 := by
    intro h
    exact integer_word_ne_zero _ _ (hφ (h.trans (map_zero φ).symm))
  have hh : φ (wordOver ℤ (I ∩ K) (J ∩ L)) * φ (wordOver ℤ (K \ I) (L \ J)) =
      φ (wordOver ℤ K L) := by
    simpa only [map_mul] using congrArg φ (word_remove_overlap ℤ I J K L)
  intro haux
  apply normPolynomial_ne_zero I J K L hI A hA
  apply hφ
  rw [map_zero, normPolynomial, map_sourceNorm]
  exact sourceNorm_zero_of_auxiliary _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
    (mixed_of_overlap _ _ _ _ _ _ hg hh h₂ hroot) haux

end PaperP1.BiquadraticWordNorm
