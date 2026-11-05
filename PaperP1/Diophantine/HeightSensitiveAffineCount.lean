module

public import PaperP1.Arithmetic.AdditiveHeightPrimeScale
public import PaperP1.Arithmetic.HeightSensitiveAffineParameters
public import PaperP1.Analysis.TruncatedAffineDegree
public import PaperP1.Diophantine.AveragedPrimeAffineCount

/-! # Affine integer-point counts retaining the actual coefficient height

The prime budget is additive in the height exponent and determinant root.
This permits the positive fibre degree to be retained in later rank bounds.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightSensitiveAffineCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap
  DegreeUniformAffineParameters

theorem uniform_count : ∃ C : ℝ, 0 < C ∧ ∀ D N κ b : ℕ,
    2 ≤ D → D ≤ N → 2 ≤ b → b ≤ D → ∀ G : ℤ[X][X],
    PlaneCurvePointCount.degree G = D → degreeY G = b → Geometric G → height G ≤ N ^ κ →
    ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
    (∀ z ∈ S, z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
      (S.card : ℝ) ≤ C * (D : ℝ) ^ 2 * (logarithmicBudget N : ℝ) *
        ((((κ + D + 1 : ℕ) : ℝ) * logarithmicBudget N) + (N : ℝ) ^ (1 / (b : ℝ))) := by
  obtain ⟨P₀, hP₀, hcount⟩ := AveragedPrimeAffineCount.uniform_bound
  obtain ⟨K, hK, hscale⟩ := AdditiveHeightPrimeScale.exists_scale P₀
  refine ⟨32 + 5760 * K, by positivity, ?_⟩
  intro D N κ b hD hDN hb hbD G hdegree hout hgeo hheight S hzero hbox
  let L := logarithmicBudget N
  let A := auxiliaryDegree N
  let b₀ := TruncatedAffineDegree.effectiveDegree b N
  let R := (N : ℝ) ^ (1 / (b : ℝ))
  let T := ((κ + D + 1 : ℕ) : ℝ) * L + R
  have hN : 1 ≤ N := by omega
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR : 0 ≤ R := by positivity
  have hne : G ≠ 0 := by
    intro hz
    have hh : PlaneCurvePointCount.degree G = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  obtain ⟨ha, _hby⟩ := GeometricBiformDegrees.integer_positive_degrees G hne hgeo (by omega)
  have haD : degreeX G ≤ D := (BivariateCurveDegrees.degreeX_le_total G).trans hdegree.le
  obtain ⟨hA, _hlogA, _hAD⟩ := auxiliary_budget D N hD hDN
  obtain ⟨hb₀, _hb₀b, hJ, haux⟩ := TruncatedAffineDegree.budget b N hb
  obtain ⟨P, m, hP, hm, hmP, hpower, hprime, hconstant, hupper⟩ := hscale (κ + 8 * D + 8) N b (by omega)
  have hlogN : Real.log N ≤ (L : ℝ) := log_le_budget N hN
  have hlog : Real.log N ≤ (A : ℝ) + 1 := by
    have he : (A : ℝ) = 3 * (L : ℝ) + 1 := by dsimp only [A, L, auxiliaryDegree]; push_cast; rfl
    linarith only [he, hlogN, hL]
  have hprimeB := TruncatedAffineDegree.prime_scale b N (N : ℝ) P hn
    (by nlinarith only [hlogN, hL]) hprime hconstant
  have hdet := AffineDeterminantUniformScale.prime_scale A b₀ hA hb₀ (N : ℝ) P hn hlog hprimeB
  have hbad : (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      (N : ℝ) ^ (degreeX G + 1) * (N : ℝ) ^ degreeY G < (P : ℝ) ^ m := by
    apply (HeightSensitiveAffineParameters.obstruction_real D N κ hD hDN G haD (by rw [hout]; exact hbD) hheight).trans_lt
    exact_mod_cast hpower
  have hx (z : ℤ × ℤ) (hz : z ∈ S) : |(z.1 : ℝ)| ≤ N := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast (hbox z hz).1
  have hy (z : ℤ × ℤ) (hz : z ∈ S) : |(z.2 : ℝ)| ≤ N := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast (hbox z hz).2
  have hc := hcount P hP m hm hmP G hne hgeo ha (by rw [hout]; omega)
    A (b₀ - 1) (by rw [hout]; exact hJ) N hn hdet hbad S hzero hx hy
  rw [hout] at hc
  have hcoeff : (((κ + 8 * D + 8 + 1 : ℕ) : ℝ)) ≤ 9 * ((κ + D + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show κ + 8 * D + 8 + 1 ≤ 9 * (κ + D + 1) by omega)
  have hPbound : (P : ℝ) ≤ 9 * K * T := by
    have hh := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (α := ℝ) L)
    have he : (((κ + 8 * D + 8 + 1 : ℕ) : ℝ)) * L + R ≤ 9 * T := by
      dsimp only [T]
      nlinarith only [hh, hR]
    exact hupper.trans (by nlinarith only [mul_le_mul_of_nonneg_left he hK.le])
  have hsumdegree : ((degreeX G : ℝ) + b) ^ 2 ≤ 4 * (D : ℝ) ^ 2 := by
    calc
      _ ≤ (2 * (D : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity)
        (by exact_mod_cast (show degreeX G + b ≤ 2 * D by omega)) 2
      _ = _ := by ring
  have hauxR : ((A + (b₀ - 1) : ℕ) : ℝ) ≤ 5 * L := by exact_mod_cast haux
  have hmain : ((degreeX G : ℝ) + b) ^ 2 * ((A + (b₀ - 1) : ℕ) : ℝ) * (32 * P) ≤
      5760 * K * (D : ℝ) ^ 2 * (L : ℝ) * T := by
    calc
      _ ≤ (4 * (D : ℝ) ^ 2) * (5 * L) * (32 * (9 * K * T)) := by gcongr
      _ = _ := by ring
  have hproduct : degreeX G * b ^ 2 ≤ D ^ 3 := by
    calc
      _ ≤ D * D ^ 2 := Nat.mul_le_mul haD (Nat.pow_le_pow_left hbD 2)
      _ = _ := by ring
  have hE : 4 * (b + 1) + 4 * (degreeX G + 1) + 8 * degreeX G * b ^ 2 ≤ 32 * D ^ 3 := by
    have hd3 : D ≤ D ^ 3 := Nat.le_self_pow (by decide) D
    nlinarith only [hproduct, hd3, hbD, haD, hD]
  have hER : (4 : ℝ) * ((b : ℝ) + 1) + 4 * ((degreeX G : ℝ) + 1) +
      8 * degreeX G * (b : ℝ) ^ 2 ≤ 32 * (D : ℝ) ^ 3 := by exact_mod_cast hE
  have hDT : (D : ℝ) ≤ T := by
    have hk : (D : ℝ) ≤ ((κ + D + 1 : ℕ) : ℝ) := by exact_mod_cast (show D ≤ κ + D + 1 by omega)
    exact (hk.trans (le_mul_of_one_le_right (by positivity) hL)).trans (le_add_of_nonneg_right hR)
  have hpoly : (D : ℝ) ^ 3 ≤ (D : ℝ) ^ 2 * L * T := by
    calc
      _ = (D : ℝ) ^ 2 * D := by ring
      _ ≤ ((D : ℝ) ^ 2 * L) * T :=
        mul_le_mul (le_mul_of_one_le_right (by positivity) hL) hDT (by positivity) (by positivity)
  have hcR : (S.card : ℝ) ≤
      4 * ((b : ℝ) + 1) + 4 * ((degreeX G : ℝ) + 1) + 8 * degreeX G * (b : ℝ) ^ 2 +
      ((degreeX G : ℝ) + b) ^ 2 * ((A + (b₀ - 1) : ℕ) : ℝ) * (32 * P) := by exact_mod_cast hc
  change (S.card : ℝ) ≤ (32 + 5760 * K) * (D : ℝ) ^ 2 * L * T
  nlinarith only [hcR, hER, hmain, mul_le_mul_of_nonneg_left hpoly (by norm_num : (0 : ℝ) ≤ 32)]


theorem uniform_normalized_count : ∃ C : ℝ, 0 < C ∧ ∀ D N κ b : ℕ,
    2 ≤ D → D ≤ N → 2 ≤ b → b ≤ D → D ≤ 2 * b → ∀ G : ℤ[X][X],
    PlaneCurvePointCount.degree G = D → degreeY G = b → Geometric G → height G ≤ N ^ κ →
    ∀ S : Finset (ℤ × ℤ), (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
    (∀ z ∈ S, z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
      (S.card : ℝ) / b ≤ C * (D : ℝ) * (logarithmicBudget N : ℝ) *
        ((((κ + D + 1 : ℕ) : ℝ) * logarithmicBudget N) + (N : ℝ) ^ (1 / (b : ℝ))) := by
  obtain ⟨C, hC, hcount⟩ := uniform_count
  refine ⟨2 * C, by positivity, ?_⟩
  intro D N κ b hD hDN hb hbD hDb G hdegree hout hgeo hheight S hzero hbox
  have hh := hcount D N κ b hD hDN hb hbD G hdegree hout hgeo hheight S hzero hbox
  have hbr : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hDbr : (D : ℝ) ≤ 2 * b := by exact_mod_cast hDb
  let L := logarithmicBudget N
  let T := ((κ + D + 1 : ℕ) : ℝ) * L + (N : ℝ) ^ (1 / (b : ℝ))
  have hprod := mul_le_mul_of_nonneg_left hDbr
    (show 0 ≤ C * (D : ℝ) * L * T by dsimp only [T]; positivity)
  apply (div_le_iff₀ hbr).mpr
  change (S.card : ℝ) ≤ (2 * C * (D : ℝ) * L * T) * b
  change (S.card : ℝ) ≤ C * (D : ℝ) ^ 2 * L * T at hh
  nlinarith only [hh, hprod]

end PaperP1.HeightSensitiveAffineCount
