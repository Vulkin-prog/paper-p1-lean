module

public import PaperP1.Arithmetic.DegreeUniformPrimeScale
public import PaperP1.Arithmetic.FixedDegreeSharpPlaneCount

/-! # A complete affine estimate with absolute polynomial degree dependence

The exponent of the degree is twelve, not the quadratic exponent required by BCN.
All prime supply, height avoidance and determinant inputs are internally proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeakDegreeUniformAffineCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap
  DegreeUniformAffineParameters

theorem uniform_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → degreeY G = D → Geometric G →
    height G ≤ N ^ (32 * D ^ 3) → ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
    (∀ z ∈ S, z.1.natAbs ≤ (D + 1) * N ∧ z.2.natAbs ≤ (D + 1) * N) →
    (S.card : ℝ) ≤ C * (D : ℝ) ^ 12 * (logarithmicBudget N : ℝ) ^ 4 *
      (N : ℝ) ^ (1 / (D : ℝ)) := by
  obtain ⟨P₀, hP₀, hcount⟩ := PolynomialPrimeAffineCount.uniform_bound
  obtain ⟨K, hK, hscale⟩ := DegreeUniformPrimeScale.exists_scale P₀
  refine ⟨32 + 32768 * K, by positivity, ?_⟩
  intro D N hD hDN G hdeg hout hgeo hheight S hzero hbox
  let L := logarithmicBudget N
  let A := auxiliaryDegree N
  let m := avoidanceCount D N
  let H := (D + 1) * N
  let R := (N : ℝ) ^ (1 / (D : ℝ))
  have hN : 1 ≤ N := by omega
  have hH : 1 ≤ H := by dsimp [H]; nlinarith
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hne : G ≠ 0 := by
    intro hz
    have hh : PlaneCurvePointCount.degree G = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  obtain ⟨ha, _hb⟩ := GeometricBiformDegrees.integer_positive_degrees G hne hgeo (by omega)
  have haD : degreeX G ≤ D := (BivariateCurveDegrees.degreeX_le_total G).trans hdeg.le
  obtain ⟨hA, hlog, hAD⟩ := auxiliary_budget D N hD hDN
  obtain ⟨P, hP, hmP, hprime, hupper⟩ := hscale D N hD hDN
  have hdet := AffineDeterminantUniformScale.prime_scale A D hA hD (H : ℝ) (P : ℝ) hHR hlog hprime
  have hbad : (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      (H : ℝ) ^ (degreeX G + 1) * (H : ℝ) ^ degreeY G < (P : ℝ) ^ m := by
    apply (obstruction_real D N hD hDN G haD hout hheight).trans_lt
    exact_mod_cast obstruction_lt_prime_power D N P (hP₀.trans hP)
  have hx (z : ℤ × ℤ) (hz : z ∈ S) : |(z.1 : ℝ)| ≤ H := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast (hbox z hz).1
  have hy (z : ℤ × ℤ) (hz : z ∈ S) : |(z.2 : ℝ)| ≤ H := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast (hbox z hz).2
  have hc := hcount P hP m hmP G hne hgeo ha (by rw [hout]; omega)
    A (D - 1) (by rw [hout]; omega) (H : ℝ) hHR hdet hbad S hzero hx hy
  rw [hout] at hc
  have hE : 4 * (D + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * D ^ 2 ≤ 32 * D ^ 3 := by
    have hmul := Nat.mul_le_mul_right (D ^ 2) haD
    have hself : D ≤ D ^ 3 := Nat.le_self_pow (by decide) D
    nlinarith
  have hER : (4 : ℝ) * ((D : ℝ) + 1) + 4 * ((degreeX G : ℝ) + 1) +
      8 * degreeX G * (D : ℝ) ^ 2 ≤ 32 * (D : ℝ) ^ 3 := by exact_mod_cast hE
  have hsumdegree : ((degreeX G : ℝ) + D) ^ 2 ≤ 4 * (D : ℝ) ^ 2 := by
    calc
      _ ≤ (2 * (D : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show degreeX G + D ≤ 2 * D by omega)) 2
      _ = _ := by ring
  have haux : ((A + (D - 1) : ℕ) : ℝ) ≤ 4 * D * L := by exact_mod_cast hAD
  have hm : (m : ℝ) ≤ 128 * (D : ℝ) ^ 3 * L := by exact_mod_cast avoidance_le D N hD
  have hT : ((degreeX G : ℝ) + D) ^ 2 * ((A + (D - 1) : ℕ) : ℝ) * (16 * m * P) ≤
      32768 * K * (D : ℝ) ^ 12 * (L : ℝ) ^ 4 * R := by
    calc
      _ ≤ (4 * (D : ℝ) ^ 2) * (4 * D * L) *
          (16 * (128 * (D : ℝ) ^ 3 * L) *
            (K * (D : ℝ) ^ 6 * (L : ℝ) ^ 2 * R)) := by gcongr
      _ = _ := by ring
  have hDpoly : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 12 * (L : ℝ) ^ 4 * R := by
    calc
      _ ≤ (D : ℝ) ^ 12 := pow_le_pow_right₀ hD1 (by decide : 3 ≤ 12)
      _ ≤ (D : ℝ) ^ 12 * (L : ℝ) ^ 4 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hR1
  have hcR : (S.card : ℝ) ≤
      4 * ((D : ℝ) + 1) + 4 * ((degreeX G : ℝ) + 1) + 8 * degreeX G * (D : ℝ) ^ 2 +
      ((degreeX G : ℝ) + D) ^ 2 * ((A + (D - 1) : ℕ) : ℝ) * (16 * m * P) := by
    exact_mod_cast hc
  change (S.card : ℝ) ≤ (32 + 32768 * K) * (D : ℝ) ^ 12 * (L : ℝ) ^ 4 * R
  nlinarith only [hcR, hER, hT, mul_le_mul_of_nonneg_left hDpoly (by norm_num : (0 : ℝ) ≤ 32)]

end PaperP1.WeakDegreeUniformAffineCount
