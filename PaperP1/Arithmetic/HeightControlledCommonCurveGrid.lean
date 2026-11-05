module

public import PaperP1.Diophantine.HeightSensitiveAffineCount
public import PaperP1.Arithmetic.FifthDegreeUniformPlaneCount
public import PaperP1.Arithmetic.IntegerCurveRationalization
public import PaperP1.Algebra.HomogenizationIrreducibilityReflection
public import PaperP1.Arithmetic.NonGeometricPlanePointBound

/-! # A normalized grid bound for the actual height-controlled common curves

The coefficient height is linear in the short-support budget. The maximum
partial degree is retained in the denominator, before any growing-degree limit.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightControlledCommonCurveGrid

open Polynomial Finset BivariateDegrees BivariateTotalDegree BivariateHeight
  CurveIntegerFibres GeometricFactorSwap DegreeUniformAffineParameters

def profile (q B : ℕ) : ℝ :=
  ((q : ℝ) ^ 2 + q * (B : ℝ) ^ (1 / 2 : ℝ)) * (logarithmicBudget B : ℝ) ^ 2

theorem height_conversion (B q : ℕ) (hB : 2 ≤ B) (G : ℤ[X][X])
    (hh : height G ≤ (B + 1) ^ (2472 * q)) : height G ≤ B ^ (4944 * q) := by
  have hb : B + 1 ≤ B ^ 2 := by nlinarith only [hB]
  calc
    _ ≤ (B + 1) ^ (2472 * q) := hh
    _ ≤ (B ^ 2) ^ (2472 * q) := Nat.pow_le_pow_left hb _
    _ = _ := by rw [← pow_mul]; congr 1; omega

theorem orient (G : ℤ[X][X]) (B : ℕ) (hgeo : Geometric G) :
    ∃ F : ℤ[X][X], Geometric F ∧
      PlaneCurvePointCount.degree F = PlaneCurvePointCount.degree G ∧
      degreeY F = max (degreeX G) (degreeY G) ∧ degreeX F ≤ degreeY F ∧
      height F = height G ∧ (integerGrid F B).card = (integerGrid G B).card := by
  by_cases hxy : degreeX G ≤ degreeY G
  · exact ⟨G, hgeo, rfl, (max_eq_right hxy).symm, hxy, rfl, rfl⟩
  · refine ⟨Bivariate.swap G, geometric_swap G hgeo,
      BivariateCurveDegreeTransport.degree_swap G, ?_, ?_, BivariateLargeRoot.height_swap G,
      grid_card_swap G B⟩
    · change degreeX G = max (degreeX G) (degreeY G)
      exact (max_eq_left (by omega)).symm
    · simpa only [degreeX, degreeY, Bivariate.swap_swap_apply] using (show degreeY G ≤ degreeX G by omega)

theorem oriented_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ B q : ℕ,
    2 ≤ B → 1 ≤ q → ∀ G : ℤ[X][X],
    2 ≤ PlaneCurvePointCount.degree G → PlaneCurvePointCount.degree G ≤ B →
    PlaneCurvePointCount.degree G ≤ 48 * q → degreeX G ≤ degreeY G →
    Geometric G → height G ≤ (B + 1) ^ (2472 * q) →
      ((integerGrid G B).card : ℝ) / degreeY G ≤ C * profile q B := by
  obtain ⟨C₀, hC₀, hsmall⟩ := FifthDegreeUniformPlaneCount.grid_geometric_count
  obtain ⟨C₁, hC₁, hlarge⟩ := HeightSensitiveAffineCount.uniform_normalized_count
  refine ⟨32 * C₀ + 240000 * C₁, by positivity, ?_⟩
  intro B q hB hq G hD hDB hDq hxy hgeo hheight
  let D := PlaneCurvePointCount.degree G
  let b := degreeY G
  let L := logarithmicBudget B
  let R := (B : ℝ) ^ (1 / 2 : ℝ)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hL : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ logarithmicBudget B by unfold logarithmicBudget; omega)
  have hR : 0 ≤ R := by positivity
  have hDb : D ≤ 2 * b := by
    have hh := totalDegree_le_partial G
    change D ≤ degreeX G + b at hh
    omega
  have hb : 1 ≤ b := by change 2 ≤ D at hD; omega
  have hp0 : 0 ≤ profile q B := by unfold profile; positivity
  have hpq : (q : ℝ) ^ 2 * (L : ℝ) ^ 2 ≤ profile q B := by
    unfold profile
    dsimp only [L]
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  have hpR : (L : ℝ) ^ 2 * R ≤ profile q B := by
    have hqr : R ≤ (q : ℝ) ^ 2 + q * R := by nlinarith only [hqR, hR, sq_nonneg (q : ℝ)]
    have hh := mul_le_mul_of_nonneg_right hqr (sq_nonneg (L : ℝ))
    simpa only [profile, L, R, mul_comm] using hh
  by_cases hb2 : 2 ≤ b
  · have hbD : b ≤ D := BivariateCurveDegrees.degreeY_le_total G
    have hzero (z : ℤ × ℤ) (hz : z ∈ PlaneCurvePointCount.grid G B) :
        G.evalEval z.1 z.2 = 0 := ((PlaneCurvePointCount.mem_grid G B z).mp hz).2.2
    have hbox (z : ℤ × ℤ) (hz : z ∈ PlaneCurvePointCount.grid G B) :
        z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B := by
      obtain ⟨hx, hy, _hz⟩ := (PlaneCurvePointCount.mem_grid G B z).mp hz
      constructor
      · have hh : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hx
        exact_mod_cast hh
      · have hh : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hy
        exact_mod_cast hh
    have hc := hlarge D B (4944 * q) b hD hDB hb2 hbD hDb G rfl rfl hgeo
      (height_conversion B q hB G hheight) (PlaneCurvePointCount.grid G B) hzero hbox
    rw [← PlaneCurvePointCount.integer_grid_card] at hc
    have hDR : (D : ℝ) ≤ 48 * q := by exact_mod_cast hDq
    have hk : (((4944 * q + D + 1 : ℕ) : ℝ)) ≤ 4993 * q := by
      exact_mod_cast (show 4944 * q + D + 1 ≤ 4993 * q by change D ≤ 48 * q at hDq; omega)
    have hroot : (B : ℝ) ^ (1 / (b : ℝ)) ≤ R :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ B by omega))
        (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb2))
    have hbound : ((integerGrid G B).card : ℝ) / b ≤
        C₁ * (48 * q) * (L : ℝ) * ((4993 * q) * L + R) := by
      apply hc.trans
      change C₁ * (D : ℝ) * (L : ℝ) *
        ((((4944 * q + D + 1 : ℕ) : ℝ)) * L + (B : ℝ) ^ (1 / (b : ℝ))) ≤ _
      gcongr
    have hL2 : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [hL]
    have hqroot : (q : ℝ) * (L : ℝ) * R ≤ (q : ℝ) * R * (L : ℝ) ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hL2 (mul_nonneg (Nat.cast_nonneg (α := ℝ) q) hR)]
    have hsum : (q : ℝ) ^ 2 * (L : ℝ) ^ 2 + q * L * R ≤ profile q B := by
      unfold profile
      dsimp only [L, R] at *
      nlinarith only [hqroot]
    have hmain : C₁ * (48 * (q : ℝ)) * (L : ℝ) * ((4993 * q) * L + R) ≤
        (240000 * C₁) * profile q B := by
      have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 240000 * C₁ by positivity)
      nlinarith only [hh, mul_nonneg hC₁.le (sq_nonneg (q : ℝ)),
        mul_nonneg (mul_nonneg hC₁.le (Nat.cast_nonneg (α := ℝ) q)) (mul_nonneg (Nat.cast_nonneg (α := ℝ) L) hR),
        mul_nonneg hC₁.le (mul_nonneg (sq_nonneg (q : ℝ)) (sq_nonneg (L : ℝ)))]
    exact (hbound.trans hmain).trans (by nlinarith only [mul_nonneg hC₀.le hp0])
  · have hb1 : b = 1 := by omega
    have hD2 : D = 2 := by change 2 ≤ D at hD; omega
    have hc := hsmall D B hD hDB G rfl hgeo
    rw [← PlaneCurvePointCount.integer_grid_card] at hc
    have hc' : ((integerGrid G B).card : ℝ) ≤ 32 * C₀ * (L : ℝ) ^ 2 * R := by
      simpa only [hD2, Nat.cast_ofNat, R, L, show (2 : ℝ) ^ 5 = 32 by norm_num, mul_assoc, mul_comm, mul_left_comm] using hc
    change ((integerGrid G B).card : ℝ) / b ≤ _
    rw [hb1, Nat.cast_one, div_one]
    have hh := mul_le_mul_of_nonneg_left hpR (show 0 ≤ 32 * C₀ by positivity)
    nlinarith only [hc', hh, mul_nonneg hC₁.le hp0]

theorem normalized_count : ∃ C : ℝ, 0 < C ∧ ∀ B q : ℕ,
    2 ≤ B → 1 ≤ q → ∀ G : ℤ[X][X], Irreducible G →
    2 ≤ PlaneCurvePointCount.degree G → PlaneCurvePointCount.degree G ≤ B →
    PlaneCurvePointCount.degree G ≤ 48 * q → height G ≤ (B + 1) ^ (2472 * q) →
      ((integerGrid G B).card : ℝ) /
        ((max (degreeX G) (degreeY G) : ℕ) : ℝ) ≤ C * profile q B := by
  obtain ⟨C, hC, hcount⟩ := oriented_geometric_count
  refine ⟨2304 + C, by positivity, ?_⟩
  intro B q hB hq G hG hD hDB hDq hheight
  have hp0 : 0 ≤ profile q B := by unfold profile; positivity
  by_cases hgeo : Geometric G
  · obtain ⟨F, hF, hdegree, hout, hxy, hheightF, hgrid⟩ := orient G B hgeo
    have hc := hcount B q hB hq F (by simpa only [hdegree] using hD)
      (by simpa only [hdegree] using hDB) (by simpa only [hdegree] using hDq)
      hxy hF (by simpa only [hheightF] using hheight)
    rw [hout, hgrid] at hc
    exact hc.trans (by nlinarith only [hp0])
  · let Q := IntegerCurveRationalization.coefficientMap (Int.castRingHom ℚ) G
    have hQ : Irreducible Q := IntegerCurveRationalization.rational_irreducible G hG (by
      change 2 ≤ totalDegree G at hD
      omega)
    have hred : ¬Irreducible (PolynomialScalarProjection.extend Q : ℂ[X][X]) := by
      intro hh
      apply hgeo
      apply (HomogenizationIrreducibilityReflection.geometric_iff_affine G hG.ne_zero).mpr
      rw [← ComplexProjectiveIrreducibility.rational_extension]
      exact hh
    have hc := NonGeometricPlanePointBound.grid_card Q hQ hred B
    have hdeg : PlaneCurvePointCount.degree Q = PlaneCurvePointCount.degree G :=
      IntegerCurveRationalization.degree_coefficientMap _ (Int.cast_injective (α := ℚ)) G
    have hgrid : PlaneCurvePointCount.grid Q B = PlaneCurvePointCount.grid G B :=
      IntegerCurveRationalization.grid_coefficientMap _ (Int.cast_injective (α := ℚ)) G B
    rw [hdeg, hgrid, ← PlaneCurvePointCount.integer_grid_card] at hc
    have hc' : ((integerGrid G B).card : ℝ) ≤ 2304 * (q : ℝ) ^ 2 := by
      have hh : (integerGrid G B).card ≤ (48 * q) ^ 2 := hc.trans (by
        calc
          _ ≤ PlaneCurvePointCount.degree G ^ 2 := by
            nlinarith only [Nat.sub_le (PlaneCurvePointCount.degree G) 1]
          _ ≤ (48 * q) ^ 2 := Nat.pow_le_pow_left hDq 2)
      exact_mod_cast (show (integerGrid G B).card ≤ 2304 * q ^ 2 by nlinarith only [hh])
    have hb : (1 : ℝ) ≤ ((max (degreeX G) (degreeY G) : ℕ) : ℝ) := by
      have hh := totalDegree_le_partial G
      change 2 ≤ totalDegree G at hD
      exact_mod_cast (show 1 ≤ max (degreeX G) (degreeY G) by omega)
    have hnorm : ((integerGrid G B).card : ℝ) /
        ((max (degreeX G) (degreeY G) : ℕ) : ℝ) ≤ (integerGrid G B).card :=
      div_le_self (by positivity) hb
    have hL : (1 : ℝ) ≤ logarithmicBudget B := by
      exact_mod_cast (show 1 ≤ logarithmicBudget B by unfold logarithmicBudget; omega)
    have hpq : (q : ℝ) ^ 2 ≤ profile q B := by
      calc
        _ ≤ (q : ℝ) ^ 2 + q * (B : ℝ) ^ (1 / 2 : ℝ) := le_add_of_nonneg_right (by positivity)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
    exact (hnorm.trans hc').trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hpq (show (0 : ℝ) ≤ 2304 by norm_num),
        mul_nonneg hC.le hp0])

end PaperP1.HeightControlledCommonCurveGrid
