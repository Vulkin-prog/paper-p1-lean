module

public import PaperP1.Arithmetic.BiquadraticWordNormDegree
public import PaperP1.Algebra.BiquadraticNormHeight
public import PaperP1.Algebra.FormalWordHeight

/-! # The actual independent-word norm has explicit height at most (B+1)^(1200q) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiquadraticWordNormHeight

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.FormalWordDegrees
  PaperP1.FormalWordHeight PaperP1.BiquadraticWordNorm PaperP1.BivariateDegrees
open scoped symmDiff

theorem height_bound (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) (B q : ℕ)
    (hq : 1 ≤ q) (hqB : q ≤ B)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (hcardx : I.card ≤ 2 * q ∧ K.card ≤ 2 * q ∧ (I ∆ K).card ≤ 2 * q)
    (hcardy : J.card ≤ 2 * q ∧ L.card ≤ 2 * q ∧ (J ∆ L).card ≤ 2 * q)
    (hAd : ∀ χ, degreeX (A χ) ≤ 3 * q ∧ degreeY (A χ) ≤ 3 * q)
    (hAh : ∀ χ, BivariateHeight.height (A χ) ≤ (B + 1) ^ (275 * q)) :
    BivariateHeight.height (normPolynomial I J K L A) ≤ (B + 1) ^ (1200 * q) := by
  let F : Fin 3 → ℤ[X][X] := ![wordOver ℤ I J, wordOver ℤ K L, wordOver ℤ (I ∆ K) (J ∆ L)]
  have hx : ∀ i ∈ I ∆ K, |i| ≤ (B : ℤ) := by
    intro i hi
    rcases mem_symmDiff.mp hi with h | h
    · exact hI i h.1
    · exact hK i h.1
  have hy : ∀ j ∈ J ∆ L, |j| ≤ (B : ℤ) := by
    intro j hj
    rcases mem_symmDiff.mp hj with h | h
    · exact hJ j h.1
    · exact hL j h.1
  have hFd : ∀ i : Fin 3, degreeX (F i) ≤ 2 * q ∧ degreeY (F i) ≤ 2 * q := by
    intro i
    fin_cases i
    · exact ⟨(word_degreeX I J).le.trans hcardx.1, (word_degreeY I J).le.trans hcardy.1⟩
    · exact ⟨(word_degreeX K L).le.trans hcardx.2.1, (word_degreeY K L).le.trans hcardy.2.1⟩
    · exact ⟨(word_degreeX _ _).le.trans hcardx.2.2, (word_degreeY _ _).le.trans hcardy.2.2⟩
  have hFh : ∀ i : Fin 3, BivariateHeight.height (F i) ≤ (B + 1) ^ (4 * q) := by
    intro i
    fin_cases i
    · exact q_height I J B q hI hJ hcardx.1 hcardy.1
    · exact q_height K L B q hK hL hcardx.2.1 hcardy.2.1
    · exact q_height _ _ B q hx hy hcardx.2.2 hcardy.2.2
  have hdK : (K \ I).card ≤ 2 * q := (card_le_card sdiff_subset).trans hcardx.2.1
  have hdL : (L \ J).card ≤ 2 * q := (card_le_card sdiff_subset).trans hcardy.2.1
  have hHd : degreeX (wordOver ℤ (K \ I) (L \ J)) ≤ 2 * q ∧
      degreeY (wordOver ℤ (K \ I) (L \ J)) ≤ 2 * q :=
    ⟨(word_degreeX _ _).le.trans hdK, (word_degreeY _ _).le.trans hdL⟩
  have hHh : BivariateHeight.height (wordOver ℤ (K \ I) (L \ J)) ≤ (B + 1) ^ (4 * q) :=
    q_height _ _ B q (fun i hi ↦ hK i (mem_sdiff.mp hi).1)
      (fun j hj ↦ hL j (mem_sdiff.mp hj).1) hdK hdL
  exact BiquadraticNormHeight.formula_height A F (wordOver ℤ (K \ I) (L \ J)) B q hq hqB
    hAd hFd hHd hAh hFh hHh

end PaperP1.BiquadraticWordNormHeight
