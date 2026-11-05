module

public import PaperP1.Arithmetic.CoarseGeometricPlaneCount
public import PaperP1.Algebra.BoundedPlaneShear

/-! # An unconditional coefficient-uniform plane exponent 2/D+epsilon

The constant depends on the fixed degree and epsilon. The sharper BCN exponent
1/D and its uniform degree dependence remain open.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedDegreePlaneCount

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.GeometricFactorSwap PaperP1.BivariateLinearShear
open PaperP1.PolynomialScalarProjection PaperP1.RationalBivariateIrreducibility

theorem fixed_outer_degree_count (D κ : ℕ) (hD : 2 ≤ D) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → Geometric G →
      degreeY G = D → ∀ H : ℝ, 2 < H → (height G : ℝ) ≤ C * H ^ κ →
        ((PlaneCurvePointCount.grid G ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (D : ℝ) + ε) := by
  classical
  obtain ⟨K, hK, hcount⟩ := HeightControlledBiformCount.uniform_first_count D D κ C ε hε
  refine ⟨K, hK, ?_⟩
  intro G hdegree hgeo houter H hH hheight
  have hne : G ≠ 0 := by
    intro hz
    have hd : PlaneCurvePointCount.degree G = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  obtain ⟨ha, hb⟩ := GeometricBiformDegrees.integer_positive_degrees G hne hgeo (by omega)
  have hA : degreeX G ≤ D := (BivariateCurveDegrees.degreeX_le_total G).trans hdegree.le
  have hB : degreeY G ≤ D := houter.le
  let S := PlaneCurvePointCount.grid G ⌊H⌋₊
  let T := S.image CoarseGeometricPlaneCount.lift
  have hc := hcount G hA hB ha hb hgeo H (by linarith) hheight T
    (by
      intro z hz
      obtain ⟨w, _hw, rfl⟩ := mem_image.mp hz
      exact CoarseGeometricPlaneCount.lift_primitive w)
    (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact CoarseGeometricPlaneCount.lift_curve G w ((PlaneCurvePointCount.mem_grid G ⌊H⌋₊ w).mp hw).2.2)
    (by
      intro z hz i
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      have hh := (PlaneCurvePointCount.mem_real_grid G H (by linarith) w).mp hw
      exact (CoarseGeometricPlaneCount.lift_box w H (by linarith) hh.1 hh.2.1 i).1)
  have hcard : T.card = S.card := card_image_of_injective _ CoarseGeometricPlaneCount.lift_injective
  rw [hcard, houter] at hc
  exact hc

theorem height_controlled_count (D κ : ℕ) (hD : 2 ≤ D) (C ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → Geometric G →
      ∀ H : ℝ, 2 < H → (height G : ℝ) ≤ C * H ^ κ →
        ((PlaneCurvePointCount.grid G ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (D : ℝ) + ε) := by
  classical
  let B : ℝ := IntegerPlaneShear.heightBudget D
  let C' := B * max 1 C
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hC' : 0 ≤ C' := mul_nonneg hB (le_trans (by norm_num) (le_max_left _ _))
  obtain ⟨K₀, hK₀, hcount⟩ := fixed_outer_degree_count D κ hD C' ε hε
  let c : ℝ := (D : ℝ) + 1
  have hc : 1 ≤ c := by
    dsimp only [c]
    linarith [Nat.cast_nonneg (α := ℝ) D]
  let K := K₀ * c ^ (2 / (D : ℝ) + ε)
  have hK : 0 ≤ K := mul_nonneg hK₀ (Real.rpow_nonneg (by linarith) _)
  refine ⟨K, hK, ?_⟩
  intro G hdegree hgeo H hH hheight
  have hne : G ≠ 0 := by
    intro hz
    have hd : PlaneCurvePointCount.degree G = 0 := by simp [PlaneCurvePointCount.degree, hz]
    omega
  obtain ⟨t, ht, houter⟩ := BoundedPlaneShear.exists_full_outer_degree G hne
  rw [hdegree] at ht houter
  let Q := shear (t : ℤ) G
  have hQdegree : PlaneCurvePointCount.degree Q = D := (shear_degree (t : ℤ) G).trans hdegree
  have hQgeo : Geometric Q := IntegerPlaneShear.geometric (t : ℤ) G hne hgeo
  have hQouter : degreeY Q = D := houter
  let L := c * H
  have hHL : H ≤ L := le_mul_of_one_le_left (by linarith) hc
  have hL : 2 < L := hH.trans_le hHL
  have hheightG : (height G : ℝ) ≤ max 1 C * H ^ κ :=
    hheight.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
  have hbudget : (height Q : ℝ) ≤ B * (height G : ℝ) := by
    dsimp only [Q, B]
    exact_mod_cast IntegerPlaneShear.height_budget D t ht G hdegree.le
  have hheightQ : (height Q : ℝ) ≤ C' * H ^ κ := by
    have hb := hbudget.trans (mul_le_mul_of_nonneg_left hheightG hB)
    simpa only [C', mul_assoc] using hb
  have hheightL : (height Q : ℝ) ≤ C' * L ^ κ := hheightQ.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hHL κ) hC')
  let S := PlaneCurvePointCount.grid G ⌊H⌋₊
  have hsub : S.image (IntegerPlaneShear.point (t : ℤ)) ⊆ PlaneCurvePointCount.grid Q ⌊L⌋₊ := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
    have hh := (PlaneCurvePointCount.mem_real_grid G H (by linarith) w).mp hw
    obtain ⟨hx, hy⟩ := IntegerPlaneShear.point_box D t ht H (by linarith) w hh.1 hh.2.1
    exact (PlaneCurvePointCount.mem_real_grid Q L (by linarith) _).mpr
      ⟨hx, hy, IntegerPlaneShear.point_zero (t : ℤ) G w hh.2.2⟩
  have hcard : S.card ≤ (PlaneCurvePointCount.grid Q ⌊L⌋₊).card := by
    rw [← card_image_of_injective S (IntegerPlaneShear.point_injective (t : ℤ))]
    exact card_le_card hsub
  have hcardR : (S.card : ℝ) ≤ ((PlaneCurvePointCount.grid Q ⌊L⌋₊).card : ℝ) := by exact_mod_cast hcard
  calc
    (S.card : ℝ) ≤ K₀ * L ^ (2 / (D : ℝ) + ε) :=
      hcardR.trans (hcount Q hQdegree hQgeo hQouter L hL hheightL)
    _ = K * H ^ (2 / (D : ℝ) + ε) := by
      dsimp only [L, K]
      rw [Real.mul_rpow (by linarith) (by linarith)]
      ring

theorem unconditional_count (D : ℕ) (hD : 2 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], PlaneCurvePointCount.degree G = D → Geometric G →
      ∀ H : ℝ, 2 < H →
        ((PlaneCurvePointCount.grid G ⌊H⌋₊).card : ℝ) ≤ K * H ^ (2 / (D : ℝ) + ε) := by
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
    have hp : (1 : ℝ) ≤ H ^ (2 / (D : ℝ) + ε) := Real.one_le_rpow (by linarith) (by positivity)
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

end PaperP1.FixedDegreePlaneCount
