module

public import PaperP1.Arithmetic.QuadraticDegreeUniformRealCount
public import PaperP1.Arithmetic.RationalRealPlaneTransport

/-! # Absolute quadratic-degree plane counts over arbitrary characteristic-zero fields -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticDegreeUniformFieldCount

open Polynomial Finset PolynomialScalarProjection DegreeUniformAffineParameters

def profile (D N : ℕ) : ℝ :=
  (D : ℝ) ^ 2 * (logarithmicBudget N : ℝ) ^ 17 * (N : ℝ) ^ (1 / (D : ℝ))

theorem degree_square_le_profile (D N : ℕ) (hN : 1 ≤ N) :
    (D : ℝ) ^ 2 ≤ profile D N := by
  have hL : (1 : ℝ) ≤ logarithmicBudget N := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (D : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  exact (le_mul_of_one_le_right (sq_nonneg (D : ℝ)) (one_le_pow₀ hL)).trans
    (le_mul_of_one_le_right (by positivity) hR)

theorem rational_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = D →
    Irreducible (extend Q : ℂ[X][X]) →
    ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ C * profile D N := by
  obtain ⟨C, hC, hcount⟩ := QuadraticDegreeUniformRealCount.grid_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hN Q hdegree hgeo
  have hb := hcount D N hD hN (extend Q : ℝ[X][X])
    ((RationalRealPlaneTransport.real_degree Q).trans hdegree)
    (RationalRealPlaneTransport.real_irreducible Q hgeo)
  simpa only [RationalRealPlaneTransport.real_grid, profile, mul_assoc] using hb

theorem rational_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = D → Irreducible Q →
    ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ C * profile D N := by
  obtain ⟨C₀, hC₀, hcount⟩ := rational_geometric_count
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro D N hD hN Q hdegree hQ
  have hprofile : 0 ≤ profile D N := (sq_nonneg (D : ℝ)).trans (degree_square_le_profile D N hN)
  by_cases hgeo : Irreducible (extend Q : ℂ[X][X])
  · have hb := hcount D N hD hN Q hdegree hgeo
    nlinarith only [hb, hprofile]
  · have hb := NonGeometricPlanePointBound.grid_card Q hQ hgeo N
    rw [hdegree] at hb
    have hc : ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ (D : ℝ) ^ 2 := by
      exact_mod_cast hb.trans (show D * (D - 1) ≤ D ^ 2 by nlinarith [Nat.sub_le D 1])
    have hd := degree_square_le_profile D N hN
    nlinarith only [hc, hd, mul_nonneg hC₀.le hprofile]

theorem field_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
    PlaneCurvePointCount.degree P = D → Irreducible P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * profile D N := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := rational_count
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro D N hD hN F _hF _hchar P hdegree hP
  let S := PlaneCurvePointCount.grid P N
  have hprofile : 0 ≤ profile D N := (sq_nonneg (D : ℝ)).trans (degree_square_le_profile D N hN)
  by_cases hsmall : S.card ≤ D ^ 2
  · have hc : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hd := degree_square_le_profile D N hN
    nlinarith only [hc, hd, mul_nonneg hC₀.le hprofile]
  let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
  have hi : Function.Injective f := by
    intro z w he
    exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
      (Int.cast_injective (congrArg Prod.snd he))
  have hpoints : ∀ z ∈ S.image f, P.evalEval (algebraMap ℚ F z.1) (algebraMap ℚ F z.2) = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hh := ((PlaneCurvePointCount.mem_grid P N w).mp hw).2.2
    simpa only [f, map_intCast] using hh
  obtain ⟨Q, hQ, _hassoc, hdeg, hzero⟩ :=
    ManyPointsScalarDescent.many_points_descent P hP (S.image f) hpoints
      (by rw [card_image_of_injective _ hi, hdegree]; omega)
  have hsub : S ⊆ PlaneCurvePointCount.grid Q N := by
    intro z hz
    have hb := (PlaneCurvePointCount.mem_grid P N z).mp hz
    exact (PlaneCurvePointCount.mem_grid Q N z).mpr
      ⟨hb.1, hb.2.1, hzero (f z) (mem_image.mpr ⟨z, hz, rfl⟩)⟩
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q N).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  have hb := hc.trans (hcount D N hD hN Q (hdeg.trans hdegree) hQ)
  nlinarith only [hb, hprofile]

theorem finite_field_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
    PlaneCurvePointCount.degree P = D → Irreducible P → ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, P.evalEval (z.1 : F) (z.2 : F) = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
    (S.card : ℝ) ≤ C * profile D N := by
  obtain ⟨C, hC, hcount⟩ := field_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hN F _hF _hchar P hdegree hP S hS
  have hsub : S ⊆ PlaneCurvePointCount.grid P N := by
    intro z hz
    obtain ⟨hzero, hx, hy⟩ := hS z hz
    apply (PlaneCurvePointCount.mem_grid P N z).mpr
    refine ⟨?_, ?_, hzero⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hx
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hy
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid P N).card : ℝ) := by exact_mod_cast card_le_card hsub
  exact hc.trans (hcount D N hD hN F P hdegree hP)

end PaperP1.QuadraticDegreeUniformFieldCount
