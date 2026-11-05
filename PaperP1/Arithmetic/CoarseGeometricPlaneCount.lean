module

public import PaperP1.Arithmetic.SmallHeightGeometricPlanePointInput
public import PaperP1.Asymptotics.HeightControlledBiformCount
public import PaperP1.Algebra.GeometricBiformDegrees
public import PaperP1.Algebra.BivariateCurveDegrees

/-! # A coefficient-uniform fixed-degree intermediate plane estimate

The exponent here is 4/D+epsilon. The stronger degree-uniform BCN exponent
1/D and its uniform degree dependence remain open.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseGeometricPlaneCount

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.BidegreeOneFibreCount PaperP1.GeometricFactorSwap
open PaperP1.PolynomialScalarProjection PaperP1.RationalBivariateIrreducibility

def lift (z : ℤ × ℤ) : Point := (![z.1, 1], ![z.2, 1])

theorem lift_injective : Function.Injective lift := by
  intro z w he
  exact Prod.ext (congrFun (congrArg Prod.fst he) 0) (congrFun (congrArg Prod.snd he) 0)

theorem lift_primitive (z : ℤ × ℤ) :
    ((lift z).1 0).natAbs.Coprime ((lift z).1 1).natAbs ∧
      ((lift z).2 0).natAbs.Coprime ((lift z).2 1).natAbs := by simp [lift]

theorem lift_curve (G : ℤ[X][X]) (z : ℤ × ℤ) (hz : G.evalEval z.1 z.2 = 0) :
    MvPolynomial.eval₂ (MvPolynomial.eval (lift z).2) (lift z).1
      (IntegerFactorProjectiveCurve.projective G) = 0 := by
  apply (IntegerPairFactorCharts.projective_zero_iff G _ _ (by simp [lift]) (by simp [lift])).mpr
  have he : BivariateEvaluation.evaluate (z.1 : ℚ) (z.2 : ℚ) G = 0 := by
    rw [BivariateEvaluation.integer_evaluation, hz, Int.cast_zero]
  simpa [lift] using he

theorem lift_box (z : ℤ × ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hx : |(z.1 : ℝ)| ≤ H) (hy : |(z.2 : ℝ)| ≤ H) :
    ∀ i, |((lift z).1 i : ℝ)| ≤ H ∧ |((lift z).2 i : ℝ)| ≤ H := by
  intro i
  fin_cases i
  · exact ⟨hx, hy⟩
  · simpa [lift] using And.intro hH hH

theorem height_controlled_count (D κ : ℕ) (hD : 2 ≤ D) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → Geometric G →
      ∀ H : ℝ, 2 < H → (height G : ℝ) ≤ C * H ^ κ →
        ((PlaneCurvePointCount.grid G ⌊H⌋₊).card : ℝ) ≤ K * H ^ (4 / (D : ℝ) + ε) := by
  classical
  obtain ⟨K₁, hK₁, hfirst⟩ := HeightControlledBiformCount.uniform_first_count D D κ C ε hε
  obtain ⟨K₂, hK₂, hsecond⟩ := HeightControlledBiformCount.uniform_second_count D D κ C ε hε
  let K := max K₁ K₂
  have hK : 0 ≤ K := hK₁.trans (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro G hdegree hgeo H hH hheight
  have hne : G ≠ 0 := by
    intro hz
    have hd : PlaneCurvePointCount.degree G = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  have hdeg : 2 ≤ PlaneCurvePointCount.degree G := by omega
  obtain ⟨ha, hb⟩ := GeometricBiformDegrees.integer_positive_degrees G hne hgeo hdeg
  have hA : degreeX G ≤ D := (BivariateCurveDegrees.degreeX_le_total G).trans hdegree.le
  have hB : degreeY G ≤ D := (BivariateCurveDegrees.degreeY_le_total G).trans hdegree.le
  have hsum : D ≤ degreeX G + degreeY G := by
    rw [← hdegree]
    exact BivariateCurveDegreeTransport.degree_le_partial_sum G
  let S := PlaneCurvePointCount.grid G ⌊H⌋₊
  let T := S.image lift
  have hcard : T.card = S.card := Finset.card_image_of_injective _ lift_injective
  have hprim : ∀ z ∈ T, (z.1 0).natAbs.Coprime (z.1 1).natAbs ∧
      (z.2 0).natAbs.Coprime (z.2 1).natAbs := by
    intro z hz
    obtain ⟨w, _hw, rfl⟩ := mem_image.mp hz
    exact lift_primitive w
  have hzero : ∀ z ∈ T, MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (IntegerFactorProjectiveCurve.projective G) = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    exact lift_curve G w ((PlaneCurvePointCount.mem_grid G ⌊H⌋₊ w).mp hw).2.2
  have hboxes : ∀ z ∈ T, ∀ i, |(z.1 i : ℝ)| ≤ H ∧ |(z.2 i : ℝ)| ≤ H := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hh := (PlaneCurvePointCount.mem_real_grid G H (by linarith) w).mp hw
    exact lift_box w H (by linarith) hh.1 hh.2.1
  have hfrac (b : ℕ) (hbpos : 0 < b) (hDb : D ≤ 2 * b) :
      (2 : ℝ) / (b : ℝ) ≤ 4 / (D : ℝ) := by
    apply (div_le_div_iff₀ (by exact_mod_cast hbpos) (by exact_mod_cast (show 0 < D by omega))).mpr
    have hh : (D : ℝ) ≤ 2 * b := by exact_mod_cast hDb
    nlinarith
  by_cases hab : degreeX G ≤ degreeY G
  · have hc := hfirst G hA hB ha hb hgeo H (by linarith) hheight T hprim hzero
      (fun z hz i ↦ (hboxes z hz i).1)
    rw [hcard] at hc
    have hpow : H ^ (2 / (degreeY G : ℝ) + ε) ≤ H ^ (4 / (D : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by
        have hh := hfrac (degreeY G) hb (by omega)
        linarith)
    exact hc.trans (mul_le_mul (le_max_left _ _) hpow (Real.rpow_nonneg (by linarith) _) hK)
  · have hc := hsecond G hA hB ha hb hgeo H (by linarith) hheight T hprim hzero
      (fun z hz i ↦ (hboxes z hz i).2)
    rw [hcard] at hc
    have hpow : H ^ (2 / (degreeX G : ℝ) + ε) ≤ H ^ (4 / (D : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by
        have hh := hfrac (degreeX G) ha (by omega)
        linarith)
    exact hc.trans (mul_le_mul (le_max_right _ _) hpow (Real.rpow_nonneg (by linarith) _) hK)

theorem unconditional_count (D : ℕ) (hD : 2 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → Geometric G →
      ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid G ⌊H⌋₊).card : ℝ) ≤ K * H ^ (4 / (D : ℝ) + ε) := by
  classical
  let r := Fintype.card (TotalDegreeMonomials.Index D)
  let κ := D * (r - 1)
  let Cnat := (6 * r) ^ (r - 1)
  let C : ℝ := Cnat
  obtain ⟨K₀, hK₀, hcount⟩ := height_controlled_count D κ hD C ε hε
  let K := max ((D : ℝ) ^ 2) K₀
  have hK : 0 ≤ K := (sq_nonneg (D : ℝ)).trans (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro G hdegree hgeo H hH
  let B := ⌊H⌋₊
  let S := PlaneCurvePointCount.grid G B
  by_cases hsmall : S.card ≤ D ^ 2
  · have hc : (S.card : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hp : (1 : ℝ) ≤ H ^ (4 / (D : ℝ) + ε) := Real.one_le_rpow (by linarith) (by positivity)
    exact hc.trans ((le_max_left _ _).trans (le_mul_of_one_le_right hK hp))
  have hne : G ≠ 0 := by
    intro hz
    have hd : PlaneCurvePointCount.degree G = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  have hRF : Irreducible (rationalize G) :=
    ScalarIrreducibilityReflection.geometric_rational_irreducible G hne hgeo
  have hAbs : Irreducible (extend (rationalize G) : ℂ[X][X]) := by
    rw [ComplexProjectiveIrreducibility.rational_extension]
    exact (HomogenizationIrreducibilityReflection.geometric_iff_affine G hne).mp hgeo
  have hB : 1 ≤ B := (Nat.one_le_floor_iff H).mpr (by linarith)
  have hbox (z : ℤ × ℤ) (hz : z ∈ S) : z.1.natAbs ≤ B ∧ z.2.natAbs ≤ B := by
    have hh := (PlaneCurvePointCount.mem_grid G B z).mp hz
    constructor
    · have hc : (z.1.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.1
      exact_mod_cast hc
    · have hc : (z.2.natAbs : ℤ) ≤ (B : ℤ) := by simpa only [Int.natCast_natAbs] using hh.2.1
      exact_mod_cast hc
  obtain ⟨Q, hQ, hQabs, hQdegree, hQheight, hQzero⟩ :=
    SmallHeightGeometricPlanePointInput.exists_small_presentation G hRF hAbs B hB S hbox
      (fun z hz ↦ ((PlaneCurvePointCount.mem_grid G B z).mp hz).2.2) (by rw [hdegree]; omega)
  have hQne : Q ≠ 0 := by
    intro hz
    apply hQ.ne_zero
    simp only [rationalize, hz, Polynomial.map_zero]
  have hQgeo : Geometric Q := (HomogenizationIrreducibilityReflection.geometric_iff_affine Q hQne).mpr (by
    rw [← ComplexProjectiveIrreducibility.rational_extension]
    exact hQabs)
  have hheight' : height Q ≤ BoundedPlaneInterpolation.heightBound D B := by
    simpa only [hdegree] using hQheight
  have hheightNat : height Q ≤ Cnat * B ^ κ :=
    hheight'.trans (BoundedPlaneInterpolation.heightBound_polynomial D B hB)
  have hheightReal : (height Q : ℝ) ≤ C * (B : ℝ) ^ κ := by
    dsimp only [C]
    exact_mod_cast hheightNat
  have hfloor : (B : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hheightH : (height Q : ℝ) ≤ C * H ^ κ := hheightReal.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor κ) (Nat.cast_nonneg Cnat))
  have hsub : S ⊆ PlaneCurvePointCount.grid Q B := by
    intro z hz
    have hh := (PlaneCurvePointCount.mem_grid G B z).mp hz
    exact (PlaneCurvePointCount.mem_grid Q B z).mpr ⟨hh.1, hh.2.1, hQzero z hz⟩
  have hc : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q B).card : ℝ) := by exact_mod_cast card_le_card hsub
  have hbound := hcount Q (hQdegree.trans hdegree) hQgeo H hH hheightH
  exact (hc.trans hbound).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (Real.rpow_nonneg (by linarith) _))

end PaperP1.CoarseGeometricPlaneCount
