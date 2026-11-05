module

public import PaperP1.Arithmetic.EfficientDegreePrimeScale
public import PaperP1.Arithmetic.FixedDegreeSharpPlaneCount
public import PaperP1.Analysis.TruncatedAffineDegree
public import PaperP1.Diophantine.AveragedPrimeAffineCount

/-! # A complete affine estimate with absolute polynomial degree dependence

The vertical auxiliary basis is truncated at the logarithmic budget.
The degree exponent is five; the original quadratic BCN bound remains open.
All prime supply, height avoidance and determinant inputs are internally proved.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FifthDegreeUniformAffineCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap
  DegreeUniformAffineParameters

theorem uniform_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → degreeY G = D → Geometric G →
    height G ≤ N ^ (32 * D ^ 3) → ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
    (∀ z ∈ S, z.1.natAbs ≤ (D + 1) * N ∧ z.2.natAbs ≤ (D + 1) * N) →
    (S.card : ℝ) ≤ C * (D : ℝ) ^ 5 * (logarithmicBudget N : ℝ) ^ 2 *
      (N : ℝ) ^ (1 / (D : ℝ)) := by
  obtain ⟨P₀, hP₀, hcount⟩ := AveragedPrimeAffineCount.uniform_bound
  obtain ⟨K, hK, hscale⟩ := EfficientDegreePrimeScale.exists_scale P₀
  refine ⟨32 + 640 * K, by positivity, ?_⟩
  intro D N hD hDN G hdeg hout hgeo hheight S hzero hbox
  let L := logarithmicBudget N
  let A := auxiliaryDegree N
  let b := TruncatedAffineDegree.effectiveDegree D N
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
  obtain ⟨hA, hlog, _hAD⟩ := auxiliary_budget D N hD hDN
  obtain ⟨hb, _hbD, hJ, hAB⟩ := TruncatedAffineDegree.budget D N hD
  obtain ⟨P, m, hP, hmpos, hmP, hPrimePower, hprime, hPconstant, hupper⟩ := hscale D N hD hDN
  have hlog3 : Real.log (H : ℝ) ≤ 3 * (L : ℝ) := by
    have hbox : (H : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast box_le_cubic D N hD hDN
    have hh := Real.log_le_log (by linarith only [hHR] : (0 : ℝ) < H) hbox
    rw [Real.log_pow] at hh
    have hl := log_le_budget N hN
    norm_num only [Nat.cast_ofNat] at hh
    change Real.log N ≤ (L : ℝ) at hl
    nlinarith only [hh, hl]
  have hprimeB := TruncatedAffineDegree.prime_scale D N (H : ℝ) P hHR hlog3 hprime hPconstant
  have hdet := AffineDeterminantUniformScale.prime_scale A b hA hb (H : ℝ) (P : ℝ) hHR hlog hprimeB
  have hbad : (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      (H : ℝ) ^ (degreeX G + 1) * (H : ℝ) ^ degreeY G < (P : ℝ) ^ m := by
    apply (obstruction_real D N hD hDN G haD hout hheight).trans_lt
    exact_mod_cast hPrimePower
  have hx (z : ℤ × ℤ) (hz : z ∈ S) : |(z.1 : ℝ)| ≤ H := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast (hbox z hz).1
  have hy (z : ℤ × ℤ) (hz : z ∈ S) : |(z.2 : ℝ)| ≤ H := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast (hbox z hz).2
  have hc := hcount P hP m hmpos hmP G hne hgeo ha (by rw [hout]; omega)
    A (b - 1) (by rw [hout]; exact hJ) (H : ℝ) hHR hdet hbad S hzero hx hy
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
  have haux : ((A + (b - 1) : ℕ) : ℝ) ≤ 5 * L := by exact_mod_cast hAB
  have hT : ((degreeX G : ℝ) + D) ^ 2 * ((A + (b - 1) : ℕ) : ℝ) * (32 * P) ≤
      640 * K * (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R := by
    calc
      _ ≤ (4 * (D : ℝ) ^ 2) * (5 * L) *
          (32 * (K * (D : ℝ) ^ 3 * (L : ℝ) * R)) := by gcongr
      _ = _ := by ring
  have hDpoly : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R := by
    calc
      _ ≤ (D : ℝ) ^ 5 := pow_le_pow_right₀ hD1 (by decide : 3 ≤ 5)
      _ ≤ (D : ℝ) ^ 5 * (L : ℝ) ^ 2 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hR1
  have hcR : (S.card : ℝ) ≤
      4 * ((D : ℝ) + 1) + 4 * ((degreeX G : ℝ) + 1) + 8 * degreeX G * (D : ℝ) ^ 2 +
      ((degreeX G : ℝ) + D) ^ 2 * ((A + (b - 1) : ℕ) : ℝ) * (32 * P) := by
    exact_mod_cast hc
  change (S.card : ℝ) ≤ (32 + 640 * K) * (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R
  nlinarith only [hcR, hER, hT, mul_le_mul_of_nonneg_left hDpoly (by norm_num : (0 : ℝ) ≤ 32)]

end PaperP1.FifthDegreeUniformAffineCount
