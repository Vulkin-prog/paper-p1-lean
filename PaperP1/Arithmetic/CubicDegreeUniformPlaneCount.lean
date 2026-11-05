module

public import PaperP1.Arithmetic.LinearHeightPlanePresentation
public import PaperP1.Arithmetic.LinearHeightShearBudget
public import PaperP1.Diophantine.HeightSensitiveAffineCount

/-! # A cubic degree-uniform bound for actual integral plane points

The coefficient height is constructed from the population rather than assumed.
One absolute constant precedes the degree, coefficients, scale and population.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CubicDegreeUniformPlaneCount

open Polynomial Finset GeometricFactorSwap DegreeUniformAffineParameters

theorem uniform_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = D → Geometric P →
    ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, P.evalEval z.1 z.2 = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
    (S.card : ℝ) ≤ C * (D : ℝ) ^ 3 * (logarithmicBudget N : ℝ) ^ 2 *
      (N : ℝ) ^ (1 / (D : ℝ)) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := HeightSensitiveAffineCount.uniform_count
  refine ⟨4 + 3000 * C₀, by positivity, ?_⟩
  intro D N hD hDN P hdegree hgeo S hS
  let L := logarithmicBudget N
  let R := (N : ℝ) ^ (1 / (D : ℝ))
  let T := (D : ℝ) ^ 3 * (L : ℝ) ^ 2 * R
  have hN : 1 ≤ N := by omega
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hT0 : 0 ≤ T := by positivity
  have hA : (D : ℝ) ^ 3 * (L : ℝ) ^ 2 ≤ T :=
    le_mul_of_one_le_right (by positivity) hR1
  have hB : (D : ℝ) ^ 2 * (L : ℝ) * R ≤ T := by
    have hd : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := pow_le_pow_right₀ hD1 (by decide : 2 ≤ 3)
    have hl : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith only [sq_nonneg ((L : ℝ) - 1), hL1]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hd hl (by positivity) (by positivity)) (by positivity)
  have hD2 : (D : ℝ) ^ 2 ≤ T := by
    calc
      _ ≤ (D : ℝ) ^ 3 := pow_le_pow_right₀ hD1 (by decide : 2 ≤ 3)
      _ ≤ (D : ℝ) ^ 3 * (L : ℝ) ^ 2 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
      _ ≤ T := hA
  by_cases hsmall : S.card ≤ 4 * D ^ 2
  · have hc : (S.card : ℝ) ≤ 4 * (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hh := mul_le_mul_of_nonneg_left hD2 (by norm_num : (0 : ℝ) ≤ 4)
    change (S.card : ℝ) ≤ (4 + 3000 * C₀) * (D : ℝ) ^ 3 * (L : ℝ) ^ 2 * R
    nlinarith only [hc, hh, mul_nonneg hC₀.le hT0]
  · obtain ⟨t, ht, Q, _hQirr, hQdegree, hQouter, hQgeo, hheight, _hassoc, hzero⟩ :=
      LinearHeightPlanePresentation.exists_presentation P D N hD hDN hdegree hgeo S hS
        (Nat.lt_of_not_ge hsmall)
    let H := (D + 1) * N
    let U := S.image (IntegerPlaneShear.point (t : ℤ))
    have hH : N ≤ H := (LinearHeightShearBudget.scale_bounds D N hD hDN).1
    have hU : U.card = S.card := card_image_of_injective _ (IntegerPlaneShear.point_injective (t : ℤ))
    have hz (z : ℤ × ℤ) (hz : z ∈ U) : Q.evalEval z.1 z.2 = 0 := by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact hzero w hw
    have hb (z : ℤ × ℤ) (hz : z ∈ U) : z.1.natAbs ≤ H ∧ z.2.natAbs ≤ H := by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact DegreeUniformPlanePresentation.point_natAbs_bounds D t ht N w (hS w hw).2.1 (hS w hw).2.2
    have hh : BivariateHeight.height Q ≤ H ^ (256 * D) :=
      hheight.trans (Nat.pow_le_pow_left hH _)
    have hc := hcount D H (256 * D) D hD (hDN.trans hH) hD le_rfl Q hQdegree
      hQouter hQgeo hh U hz hb
    rw [hU] at hc
    have hlog : (logarithmicBudget H : ℝ) ≤ 3 * (L : ℝ) := by
      exact_mod_cast LinearHeightShearBudget.logarithmic_bound D N hD hDN
    have hroot : (H : ℝ) ^ (1 / (D : ℝ)) ≤ 2 * R :=
      LinearHeightShearBudget.root_scale D N (by omega)
    have hcoef : ((256 * D + D + 1 : ℕ) : ℝ) ≤ 258 * (D : ℝ) := by
      exact_mod_cast (show 256 * D + D + 1 ≤ 258 * D by omega)
    have hbound : (S.card : ℝ) ≤
        2322 * C₀ * ((D : ℝ) ^ 3 * (L : ℝ) ^ 2) +
          6 * C₀ * ((D : ℝ) ^ 2 * (L : ℝ) * R) := by
      calc
        _ ≤ C₀ * (D : ℝ) ^ 2 * (logarithmicBudget H : ℝ) *
            (((256 * D + D + 1 : ℕ) : ℝ) * logarithmicBudget H + (H : ℝ) ^ (1 / (D : ℝ))) := hc
        _ ≤ C₀ * (D : ℝ) ^ 2 * (3 * L) * (258 * D * (3 * L) + 2 * R) := by gcongr
        _ = _ := by ring
    have ha := mul_le_mul_of_nonneg_left hA (show 0 ≤ 2322 * C₀ by positivity)
    have hb' := mul_le_mul_of_nonneg_left hB (show 0 ≤ 6 * C₀ by positivity)
    change (S.card : ℝ) ≤ (4 + 3000 * C₀) * (D : ℝ) ^ 3 * (L : ℝ) ^ 2 * R
    nlinarith only [hbound, ha, hb', hT0, mul_nonneg hC₀.le hT0]

theorem grid_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = D → Geometric P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * (D : ℝ) ^ 3 *
      (logarithmicBudget N : ℝ) ^ 2 * (N : ℝ) ^ (1 / (D : ℝ)) := by
  obtain ⟨C, hC, h⟩ := uniform_geometric_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hDN P hdegree hgeo
  apply h D N hD hDN P hdegree hgeo (PlaneCurvePointCount.grid P N)
  intro z hz
  obtain ⟨hx, hy, hzero⟩ := (PlaneCurvePointCount.mem_grid P N z).mp hz
  refine ⟨hzero, ?_, ?_⟩
  · have hh : (z.1.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hx
    exact_mod_cast hh
  · have hh : (z.2.natAbs : ℤ) ≤ (N : ℤ) := by simpa only [Int.natCast_natAbs] using hy
    exact_mod_cast hh

end PaperP1.CubicDegreeUniformPlaneCount
