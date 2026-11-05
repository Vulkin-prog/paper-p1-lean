module

public import PaperP1.Arithmetic.FifthDegreeUniformPlaneCount
public import PaperP1.Arithmetic.FixedDegreeSharpFieldPlaneCount
public import PaperP1.Arithmetic.LinearPlaneGridBound

/-! # Absolute polynomial-degree plane counts over every characteristic-zero field

Scalar descent needs no complex embedding of the original coefficient field.
The weaker fifth degree power is retained explicitly throughout.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FifthDegreeUniformFieldCount

open Polynomial Finset PolynomialScalarProjection RationalBivariateIrreducibility
  GeometricFactorSwap DegreeUniformAffineParameters

def profile (D N : ℕ) : ℝ :=
  (D : ℝ) ^ 5 * (logarithmicBudget N : ℝ) ^ 2 * (N : ℝ) ^ (1 / (D : ℝ))

theorem degree_square_le_profile (D N : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) :
    (D : ℝ) ^ 2 ≤ profile D N := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hL1 : (1 : ℝ) ≤ logarithmicBudget N := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / (D : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  calc
    _ ≤ (D : ℝ) ^ 5 := pow_le_pow_right₀ hD1 (by decide : 2 ≤ 5)
    _ ≤ (D : ℝ) ^ 5 * (logarithmicBudget N : ℝ) ^ 2 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hR1

theorem rational_geometric_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = D → Irreducible Q →
    Irreducible (extend Q : ℂ[X][X]) →
    ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ C * profile D N := by
  obtain ⟨C, hC, hcount⟩ := FifthDegreeUniformPlaneCount.grid_geometric_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hDN Q hdegree hQ hgeo
  obtain ⟨F, n, hn, hF⟩ := IntegralGeometricPlanePointInput.exists_integral_presentation Q
  obtain ⟨hRF, hgeoF, hdeg, hgrid⟩ :=
    IntegralGeometricPlanePointInput.presentation_properties Q hQ hgeo F n hn hF
  have hFne : F ≠ 0 := by
    intro hz
    apply hRF.ne_zero
    simp only [rationalize, hz, Polynomial.map_zero]
  have hFgeo : Geometric F :=
    (HomogenizationIrreducibilityReflection.geometric_iff_affine F hFne).mpr (by
      rw [← ComplexProjectiveIrreducibility.rational_extension]
      exact hgeoF)
  have hb := hcount D N hD hDN F (hdeg.trans hdegree) hFgeo
  simpa only [hgrid, profile, mul_assoc] using hb

theorem rational_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = D → Irreducible Q →
    ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ C * profile D N := by
  obtain ⟨C₀, hC₀, hcount⟩ := rational_geometric_count
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro D N hD hDN Q hdegree hQ
  have hprofile : 0 ≤ profile D N := (sq_nonneg (D : ℝ)).trans
    (degree_square_le_profile D N (by omega) (by omega))
  by_cases hgeo : Irreducible (extend Q : ℂ[X][X])
  · have hb := hcount D N hD hDN Q hdegree hQ hgeo
    nlinarith only [hb, hprofile]
  · have hb := NonGeometricPlanePointBound.grid_card Q hQ hgeo N
    rw [hdegree] at hb
    have hc : ((PlaneCurvePointCount.grid Q N).card : ℝ) ≤ (D : ℝ) ^ 2 := by
      exact_mod_cast hb.trans (show D * (D - 1) ≤ D ^ 2 by nlinarith [Nat.sub_le D 1])
    have hd := degree_square_le_profile D N (by omega) (by omega)
    nlinarith only [hc, hd, mul_nonneg hC₀.le hprofile]

theorem field_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
    PlaneCurvePointCount.degree P = D → Irreducible P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * profile D N := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := rational_count
  refine ⟨1 + C₀, by positivity, ?_⟩
  intro D N hD hDN F _hF _hchar P hdegree hP
  let S := PlaneCurvePointCount.grid P N
  have hprofile : 0 ≤ profile D N := (sq_nonneg (D : ℝ)).trans
    (degree_square_le_profile D N (by omega) (by omega))
  by_cases hsmall : S.card ≤ D ^ 2
  · have hc : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hd := degree_square_le_profile D N (by omega) (by omega)
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
  have hb := hc.trans (hcount D N hD hDN Q (hdeg.trans hdegree) hQ)
  nlinarith only [hb, hprofile]

theorem global_field_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
    PlaneCurvePointCount.degree P = D → Irreducible P →
    ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ C * profile D N := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := field_count
  refine ⟨9 + C₀, by positivity, ?_⟩
  intro D N hD hN F _hF _hchar P hdegree hP
  have hd := degree_square_le_profile D N (by omega) hN
  have hprofile : 0 ≤ profile D N := (sq_nonneg (D : ℝ)).trans hd
  by_cases hDN : D ≤ N
  · have hb := hcount D N hD hDN F P hdegree hP
    nlinarith only [hb, hprofile]
  · have hc : (PlaneCurvePointCount.grid P N).card ≤ (2 * N + 1) ^ 2 := by
      calc
        _ ≤ ((CurveIntegerFibres.offsetBox N) ×ˢ (CurveIntegerFibres.offsetBox N)).card :=
          card_le_card (filter_subset _ _)
        _ = _ := by rw [card_product, LinearPlaneGridBound.offsetBox_card, pow_two]
    have hsize : (2 * N + 1) ^ 2 ≤ 9 * D ^ 2 := by
      calc
        _ ≤ (3 * D) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = _ := by ring
    have hcR : ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ 9 * (D : ℝ) ^ 2 := by
      exact_mod_cast hc.trans hsize
    have hscaled := mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 9)
    nlinarith only [hcR, hscaled, mul_nonneg hC₀.le hprofile]

theorem finite_field_count : ∃ C : ℝ, 0 < C ∧ ∀ D N : ℕ, 2 ≤ D → 1 ≤ N →
    ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
    PlaneCurvePointCount.degree P = D → Irreducible P → ∀ S : Finset (ℤ × ℤ),
    (∀ z ∈ S, P.evalEval (z.1 : F) (z.2 : F) = 0 ∧ z.1.natAbs ≤ N ∧ z.2.natAbs ≤ N) →
    (S.card : ℝ) ≤ C * profile D N := by
  obtain ⟨C, hC, h⟩ := global_field_count
  refine ⟨C, hC, ?_⟩
  intro D N hD hN F _hF _hchar P hdegree hP S hS
  have hsub : S ⊆ PlaneCurvePointCount.grid P N := by
    intro z hz
    have hh := hS z hz
    apply (PlaneCurvePointCount.mem_grid P N z).mpr
    refine ⟨?_, ?_, hh.1⟩
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.1
    · rw [Int.abs_eq_natAbs]
      exact_mod_cast hh.2.2
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid P N).card : ℝ) := by exact_mod_cast card_le_card hsub
  exact hc.trans (h D N hD hN F P hdegree hP)

end PaperP1.FifthDegreeUniformFieldCount
