module

public import PaperP1.Arithmetic.FixedDegreePlaneCount

/-! # An unconditional fixed-degree count over arbitrary characteristic-zero fields

The constant precedes the coefficient field and the equation. The exponent
2/D+epsilon is weaker than the remaining degree-uniform BCN target.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedDegreeFieldPlaneCount

open Polynomial Finset PaperP1.PolynomialScalarProjection
open PaperP1.RationalBivariateIrreducibility PaperP1.GeometricFactorSwap

theorem rational_geometric_count (D : ℕ) (hD : 2 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = D →
      Irreducible Q → Irreducible (extend Q : ℂ[X][X]) → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid Q ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (D : ℝ) + ε) := by
  obtain ⟨K, hK, hcount⟩ := FixedDegreePlaneCount.unconditional_count D hD ε hε
  refine ⟨K, hK, ?_⟩
  intro Q hdegree hQ hgeo H hH
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
  have hb := hcount F (hdeg.trans hdegree) hFgeo H hH
  simpa only [hgrid] using hb

theorem rational_count (D : ℕ) (hD : 2 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℚ[X][X], PlaneCurvePointCount.degree Q = D →
      Irreducible Q → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid Q ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (D : ℝ) + ε) := by
  obtain ⟨K₀, hK₀, hcount⟩ := rational_geometric_count D hD ε hε
  let K := max ((D : ℝ) ^ 2) K₀
  have hK : 0 ≤ K := hK₀.trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro Q hdegree hQ H hH
  by_cases hgeo : Irreducible (extend Q : ℂ[X][X])
  · exact (hcount Q hdegree hQ hgeo H hH).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))
  · have hb := NonGeometricPlanePointBound.grid_card Q hQ hgeo ⌊H⌋₊
    rw [hdegree] at hb
    have hc : ((PlaneCurvePointCount.grid Q ⌊H⌋₊).card : ℝ) ≤ (D : ℝ) ^ 2 := by
      exact_mod_cast hb.trans (show D * (D - 1) ≤ D ^ 2 by nlinarith [Nat.sub_le D 1])
    have hp : (1 : ℝ) ≤ H ^ (2 / (D : ℝ) + ε) :=
      Real.one_le_rpow (by linarith) (by positivity)
    exact hc.trans ((le_max_left _ _).trans (le_mul_of_one_le_right hK hp))

theorem field_count (D : ℕ) (hD : 2 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = D → Irreducible P → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (D : ℝ) + ε) := by
  classical
  obtain ⟨K₀, hK₀, hcount⟩ := rational_count D hD ε hε
  let K := max ((D : ℝ) ^ 2) K₀
  have hK : 0 ≤ K := hK₀.trans (le_max_right _ _)
  refine ⟨K, hK, ?_⟩
  intro F _hF _hchar P hdegree hP H hH
  let S := PlaneCurvePointCount.grid P ⌊H⌋₊
  by_cases hsmall : S.card ≤ D ^ 2
  · have hc : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hp : (1 : ℝ) ≤ H ^ (2 / (D : ℝ) + ε) :=
      Real.one_le_rpow (by linarith) (by positivity)
    exact hc.trans ((le_max_left _ _).trans (le_mul_of_one_le_right hK hp))
  let f : ℤ × ℤ → ℚ × ℚ := fun z ↦ ((z.1 : ℚ), (z.2 : ℚ))
  have hi : Function.Injective f := by
    intro z w he
    exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
      (Int.cast_injective (congrArg Prod.snd he))
  have hpoints : ∀ z ∈ S.image f, P.evalEval (algebraMap ℚ F z.1) (algebraMap ℚ F z.2) = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hh := ((PlaneCurvePointCount.mem_grid P ⌊H⌋₊ w).mp hw).2.2
    simpa only [f, map_intCast] using hh
  obtain ⟨Q, hQ, _hassoc, hdeg, hzero⟩ :=
    ManyPointsScalarDescent.many_points_descent P hP (S.image f) hpoints
      (by rw [card_image_of_injective _ hi, hdegree]; omega)
  have hsub : S ⊆ PlaneCurvePointCount.grid Q ⌊H⌋₊ := by
    intro z hz
    have hb := (PlaneCurvePointCount.mem_grid P ⌊H⌋₊ z).mp hz
    exact (PlaneCurvePointCount.mem_grid Q ⌊H⌋₊ z).mpr
      ⟨hb.1, hb.2.1, hzero (f z) (mem_image.mpr ⟨z, hz, rfl⟩)⟩
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q ⌊H⌋₊).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  exact (hc.trans (hcount Q (hdeg.trans hdegree) hQ H hH)).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))

theorem bounded_degree_count (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      2 ≤ PlaneCurvePointCount.degree P → PlaneCurvePointCount.degree P ≤ M →
      Irreducible P → ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid P ⌊H⌋₊).card : ℝ) ≤
          K * H ^ (2 / (PlaneCurvePointCount.degree P : ℝ) + ε) := by
  classical
  choose c hc hcount using fun d : ℕ ↦ field_count (d + 2) (by omega) ε hε
  let K := ∑ d ∈ range (M + 1), c d
  have hK : 0 ≤ K := Finset.sum_nonneg (fun d _hd ↦ hc d)
  refine ⟨K, hK, ?_⟩
  intro F _hF _hchar P hD hM hP H hH
  let d := PlaneCurvePointCount.degree P - 2
  have hd : d + 2 = PlaneCurvePointCount.degree P := Nat.sub_add_cancel hD
  have hmem : d ∈ range (M + 1) := mem_range.mpr (by dsimp only [d]; omega)
  have hle : c d ≤ K := single_le_sum (fun i _hi ↦ hc i) hmem
  have hb := hcount d F P hd.symm hP H hH
  rw [hd] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (by linarith) _))

end PaperP1.FixedDegreeFieldPlaneCount
