module

public import PaperP1.Arithmetic.TwoWitnessTheorem
public import PaperP1.Arithmetic.EvenWordRanks
public import PaperP1.Arithmetic.CommonCurveFamily

/-! # The actual pair norms for the bounded even basis of the common-curve theorem -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoWitnessFromSupports

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree PaperP1.BivariateHeight
  PaperP1.FormalWordPolynomials PaperP1.BiquadraticWordNorm PaperP1.EvenWordRanks

theorem exists_norm (B q₀ : ℕ) (hq : 1 ≤ q₀) (hqB : q₀ ≤ B)
    (I J K L : Finset ℤ) (hind : Independent I J K L)
    (heven : Even I.card ∧ Even J.card ∧ Even K.card ∧ Even L.card)
    (hcard : I.card ≤ 2 * q₀ ∧ J.card ≤ 2 * q₀ ∧ K.card ≤ 2 * q₀ ∧ L.card ≤ 2 * q₀)
    (hI : ∀ i ∈ I, |i| ≤ (B : ℤ)) (hJ : ∀ j ∈ J, |j| ≤ (B : ℤ))
    (hK : ∀ i ∈ K, |i| ≤ (B : ℤ)) (hL : ∀ j ∈ L, |j| ≤ (B : ℤ))
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : ((B : ℝ) + 1) ^ (1000000 * q₀ ^ 2) < N)
    (h₁ : IsSquare ((wordOver ℤ I J).evalEval x y)) (h₂ : IsSquare ((wordOver ℤ K L).evalEval x y)) :
    ∃ A : Fin 4 → ℤ[X][X],
      (∀ E : ℤ[X][X], (∀ χ, E ∣ A χ) → IsUnit E) ∧ (∃ χ, A χ ≠ 0) ∧
      (∀ χ, height (A χ) ≤ (B + 1) ^ (550 * q₀)) ∧
      normPolynomial I J K L A ≠ 0 ∧ (normPolynomial I J K L A).evalEval x y = 0 ∧
      degreeX (normPolynomial I J K L A) ≤ 24 * q₀ ∧ degreeY (normPolynomial I J K L A) ≤ 24 * q₀ ∧
      totalDegree (normPolynomial I J K L A) ≤ 48 * q₀ ∧
      height (normPolynomial I J K L A) ≤ (B + 1) ^ (2400 * q₀) ∧
      WordNormCertificate.Certificate I J K L A (normPolynomial I J K L A) := by
  let q := min (2 * q₀) B
  have hq₁ : 1 ≤ q := by dsimp [q]; omega
  have hq₂ : q ≤ B := min_le_right _ _
  have hqsmall : q ≤ 2 * q₀ := min_le_left _ _
  have hr := pairRanks_bound I K B q₀ heven.1 heven.2.2.1 hI hK hcard.1 hcard.2.2.1
  have hs := pairRanks_bound J L B q₀ heven.2.1 heven.2.2.2 hJ hL hcard.2.1 hcard.2.2.2
  have hnat : (B + 1) ^ (1200 * q) ≤ (B + 1) ^ (1000000 * q₀ ^ 2) :=
    (Nat.pow_le_pow_right (by omega) (by omega : 1200 * q ≤ 2472 * q₀)).trans
      (CommonCurveFamily.linear_threshold B q₀ hq)
  have hreal : ((B : ℝ) + 1) ^ (1200 * q) ≤ ((B : ℝ) + 1) ^ (1000000 * q₀ ^ 2) := by exact_mod_cast hnat
  obtain ⟨A, R, hprimitive, hA, hAH, hR, hne, hzero, hdx, hdy, hdt, hRH, hcert⟩ :=
    TwoWitnessTheorem.integer_radius B hq₁ hq₂ hr hs I J K L hind hI hJ hK hL
      (pairRanks_cards I K heven.1 heven.2.2.1) (pairRanks_cards J L heven.2.1 heven.2.2.2)
      N x y hx hy hx₂ hy₂ (hreal.trans_lt hlarge) h₁ h₂
  subst R
  refine ⟨A, hprimitive, hA, ?_, hne, hzero, ?_, ?_, ?_, ?_, hcert⟩
  · intro χ
    exact (hAH χ).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · omega
  · omega
  · omega
  · exact hRH.trans (Nat.pow_le_pow_right (by omega) (by omega))

end PaperP1.TwoWitnessFromSupports
