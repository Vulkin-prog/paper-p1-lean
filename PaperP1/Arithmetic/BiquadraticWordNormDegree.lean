module

public import PaperP1.Arithmetic.BiquadraticWordNorm
public import PaperP1.Arithmetic.BiquadraticRungeMatrix
public import PaperP1.Algebra.BiquadraticNormDegree
public import PaperP1.Algebra.FormalWordDegrees
public import PaperP1.Algebra.BivariateTotalDegree

/-! # The literal independent-word norm has the source partial degrees 12q and total degree 24q -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticWordNormDegree

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.FormalWordDegrees
  PaperP1.BiquadraticWordNorm PaperP1.BiquadraticSourceNorm PaperP1.BivariateDegrees
  PaperP1.BivariateTotalDegree PaperP1.BiquadraticRungeMatrix
open scoped symmDiff

theorem partial_bounds (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X])
    (kx ky : ℕ) (r s : Fin 3 → ℕ)
    (hr : ∀ i, r i ≤ kx) (hs : ∀ i, s i ≤ ky)
    (hcardx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcardy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (hA₀ : degreeX (A 0) ≤ kx ∧ degreeY (A 0) ≤ ky)
    (hA : ∀ i : Fin 3, degreeX (A i.succ) ≤ kx - r i ∧ degreeY (A i.succ) ≤ ky - s i) :
    degreeX (normPolynomial I J K L A) ≤ 4 * kx ∧
      degreeY (normPolynomial I J K L A) ≤ 4 * ky := by
  have hxH := quotient_rank_balance I K (r 0) (r 1) (r 2) hcardx.1 hcardx.2.1 hcardx.2.2
  have hyH := quotient_rank_balance J L (s 0) (s 1) (s 2) hcardy.1 hcardy.2.1 hcardy.2.2
  constructor
  · change (Bivariate.swap (normPolynomial I J K L A)).natDegree ≤ 4 * kx
    rw [normPolynomial, map_sourceNorm]
    apply BiquadraticNormDegree.norm_bound _ _ _ _ _ _ _ _ kx (r 0) (r 1) (r 2)
      (hr 0) (hr 1) (hr 2) hA₀.1 (hA 0).1 (hA 1).1 (hA 2).1
    · exact le_of_eq ((word_degreeX I J).trans hcardx.1)
    · exact le_of_eq ((word_degreeX K L).trans hcardx.2.1)
    · exact le_of_eq ((word_degreeX _ _).trans hcardx.2.2)
    · change degreeX (wordOver ℤ (K \ I) (L \ J)) + r 0 ≤ r 1 + r 2
      rw [word_degreeX, hxH]
  · change (normPolynomial I J K L A).natDegree ≤ 4 * ky
    rw [normPolynomial]
    apply BiquadraticNormDegree.norm_bound _ _ _ _ _ _ _ _ ky (s 0) (s 1) (s 2)
      (hs 0) (hs 1) (hs 2) hA₀.2 (hA 0).2 (hA 1).2 (hA 2).2
    · exact le_of_eq ((word_degreeY I J).trans hcardy.1)
    · exact le_of_eq ((word_degreeY K L).trans hcardy.2.1)
    · exact le_of_eq ((word_degreeY _ _).trans hcardy.2.2)
    · change degreeY (wordOver ℤ (K \ I) (L \ J)) + s 0 ≤ s 1 + s 2
      rw [word_degreeY, hyH]

theorem q_bounds (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) (q : ℕ) (r s : Fin 3 → ℕ)
    (hr : ∀ i, r i ≤ q) (hs : ∀ i, s i ≤ q)
    (hcardx : I.card = 2 * r 0 ∧ K.card = 2 * r 1 ∧ (I ∆ K).card = 2 * r 2)
    (hcardy : J.card = 2 * s 0 ∧ L.card = 2 * s 1 ∧ (J ∆ L).card = 2 * s 2)
    (hA : ∀ χ : Fin 4, degreeX (A χ) ≤ 3 * q - blockRank r χ ∧
      degreeY (A χ) ≤ 3 * q - blockRank s χ) :
    degreeX (normPolynomial I J K L A) ≤ 12 * q ∧
      degreeY (normPolynomial I J K L A) ≤ 12 * q ∧
        totalDegree (normPolynomial I J K L A) ≤ 24 * q := by
  have hr' : ∀ i, r i ≤ 3 * q := fun i ↦ (hr i).trans (by omega)
  have hs' : ∀ i, s i ≤ 3 * q := fun i ↦ (hs i).trans (by omega)
  have h₀ : degreeX (A 0) ≤ 3 * q ∧ degreeY (A 0) ≤ 3 * q := by
    simpa only [blockRank, Fin.cases_zero, Nat.sub_zero] using hA 0
  have hi : ∀ i : Fin 3, degreeX (A i.succ) ≤ 3 * q - r i ∧
      degreeY (A i.succ) ≤ 3 * q - s i := fun i ↦ hA i.succ
  have hp := partial_bounds I J K L A (3 * q) (3 * q) r s hr' hs' hcardx hcardy h₀ hi
  have ht := totalDegree_le_partial (normPolynomial I J K L A)
  omega

end PaperP1.BiquadraticWordNormDegree
