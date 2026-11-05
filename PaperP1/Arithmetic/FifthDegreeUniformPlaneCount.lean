module

public import PaperP1.Diophantine.FifthDegreeUniformAffineCount

/-! # A coefficient-uniform polynomial-degree bound for actual integral plane points

One absolute constant precedes the degree, coefficients, scale and population.
The fifth degree power is weaker than BCN and does not establish its consequences.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FifthDegreeUniformPlaneCount

open Polynomial Finset GeometricFactorSwap DegreeUniformAffineParameters

theorem uniform_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = D → Geometric P →
    ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, P.evalEval z.1 z.2 = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
    (S.card : ℝ) ≤ C * (D : ℝ) ^ 5 * (logarithmicBudget N : ℝ) ^ 2 *
      (N : ℝ) ^ (1 / (D : ℝ)) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := FifthDegreeUniformAffineCount.uniform_count
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro D N hD hDN P hdegree hgeo S hS
  let L := logarithmicBudget N
  let R := (N : ℝ) ^ (1 / (D : ℝ))
  have hN : 1 ≤ N := by omega
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hpoly0 : 0 ≤ (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R := by positivity
  by_cases hsmall : S.card ≤ D ^ 2
  · have hcard : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hpoly : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R := by
      calc
        _ ≤ (D : ℝ) ^ 5 := pow_le_pow_right₀ hD1 (by decide : 2 ≤ 5)
        _ ≤ (D : ℝ) ^ 5 * (L : ℝ) ^ 2 :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hR1
    change (S.card : ℝ) ≤ (1 + C₀) * (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R
    nlinarith only [hcard, hpoly, mul_nonneg hC₀.le hpoly0]
  · obtain ⟨t, ht, Q, hQdegree, hQouter, hQgeo, hheight, _hassoc, hzero⟩ :=
      DegreeUniformPlanePresentation.exists_presentation P D N hD hDN hdegree hgeo S hS
        (Nat.lt_of_not_ge hsmall)
    let U := S.image (IntegerPlaneShear.point (t : ℤ))
    have hU : U.card = S.card := card_image_of_injective _ (IntegerPlaneShear.point_injective (t : ℤ))
    have hz (z : ℤ × ℤ) (hz : z ∈ U) : Q.evalEval z.1 z.2 = 0 := by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact hzero w hw
    have hb (z : ℤ × ℤ) (hz : z ∈ U) :
        z.1.natAbs ≤ (D + 1) * N ∧ z.2.natAbs ≤ (D + 1) * N := by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact DegreeUniformPlanePresentation.point_natAbs_bounds D t ht N w (hS w hw).2.1 (hS w hw).2.2
    have hc := hcount D N hD hDN Q hQdegree hQouter hQgeo hheight U hz hb
    rw [hU] at hc
    change (S.card : ℝ) ≤ (1 + C₀) * (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R
    change (S.card : ℝ) ≤ C₀ * (D : ℝ) ^ 5 * (L : ℝ) ^ 2 * R at hc
    nlinarith only [hc, hpoly0]

theorem grid_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ P : ℤ[X][X], PlaneCurvePointCount.degree P = D → Geometric P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * (D : ℝ) ^ 5 *
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

end PaperP1.FifthDegreeUniformPlaneCount
