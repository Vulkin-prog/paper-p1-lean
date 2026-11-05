module

public import PaperP1.Algebra.HomogeneousChartSpecialization
public import PaperP1.Algebra.ScalarIrreducibilityReflection
public import PaperP1.Diophantine.LinearProjectiveFactor
public import PaperP1.Diophantine.PrimitiveHomogeneousZeros

/-! # Nonzero projective fibres of the actual geometric biform

The axis branch uses a literal leading coefficient. The nonaxis branch uses
rational affine irreducibility and specialization, with no point-count input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricProjectiveFibres

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.IntegerFactorProjectiveCurve
  PaperP1.GeometricFactorSwap PaperP1.HomogeneousCharts PaperP1.PrimitiveDirections

def fibre (G : ℤ[X][X]) (x : Pair) : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.map (MvPolynomial.eval x) (projective (Bivariate.swap G))

theorem fibre_evaluation (G : ℤ[X][X]) (x y : Pair) :
    MvPolynomial.eval y (fibre G x) =
      MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) := by
  rw [fibre, MvPolynomial.eval_map]
  exact PaperP1.BivariateProjectiveSwap.evaluation_swap G x y

theorem fibre_homogeneous (G : ℤ[X][X]) (x : Pair) :
    (fibre G x).IsHomogeneous (degreeY G) := by
  have hh : (projective (Bivariate.swap G)).IsHomogeneous (degreeY G) := by
    rw [← PaperP1.BivariateProjectiveSwap.degreeX_swap G]
    exact projective_homogeneous _
  exact hh.map (MvPolynomial.eval x)

theorem fibre_chart_coefficient (G : ℤ[X][X]) (x : Pair) (j : ℕ) (hj : j ≤ degreeY G) :
    (chart (fibre G x)).coeff j = MvPolynomial.eval x ((G.coeff j).homogenize (degreeX G)) := by
  have hj' : j < degreeX (Bivariate.swap G) + 1 := by
    rw [PaperP1.BivariateProjectiveSwap.degreeX_swap]
    omega
  have hc := PaperP1.LinearProjectiveFactor.projective_chart_coefficient
    (Bivariate.swap G) ⟨j, hj'⟩
  rw [fibre, PaperP1.HomogeneousChartSpecialization.chart_map _ _
    (projective_homogeneous _) _, Polynomial.coeff_map, hc,
    Bivariate.swap_swap_apply, PaperP1.BivariateProjectiveSwap.degreeY_swap]

theorem fibre_axis_nonzero (G : ℤ[X][X]) (hG : G ≠ 0) (x : Pair)
    (hx₀ : x 0 ≠ 0) (hx₁ : x 1 = 0) : fibre G x ≠ 0 := by
  have hswap : Bivariate.swap G ≠ 0 := by
    intro hz
    apply hG
    exact (Bivariate.swap (R := ℤ)).injective (hz.trans (map_zero _).symm)
  have hrow : (Bivariate.swap G).coeff (degreeX G) ≠ 0 := by
    change (Bivariate.swap G).coeff (Bivariate.swap G).natDegree ≠ 0
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hswap
  let j := ((Bivariate.swap G).coeff (degreeX G)).natDegree
  have hc : (G.coeff j).coeff (degreeX G) ≠ 0 := by
    rw [← PaperP1.BivariateIrreducibleHomogenization.swap_coefficient]
    change ((Bivariate.swap G).coeff (degreeX G)).coeff
      ((Bivariate.swap G).coeff (degreeX G)).natDegree ≠ 0
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hrow
  have hGcoeff : G.coeff j ≠ 0 := fun hz ↦ hc (by rw [hz, coeff_zero])
  have hj : j ≤ degreeY G := Polynomial.le_natDegree_of_ne_zero hGcoeff
  intro hz
  have he : MvPolynomial.eval x ((G.coeff j).homogenize (degreeX G)) = 0 := by
    rw [← fibre_chart_coefficient G x j hj, hz]
    simp [chart]
  have hx : x = ![x 0, 0] := by
    funext i
    fin_cases i
    · rfl
    · exact hx₁
  rw [hx, PaperP1.HomogeneousChartSpecialization.eval_homogenize_axis] at he
  exact mul_ne_zero hc (pow_ne_zero _ hx₀) he

theorem fibre_nonaxis_nonzero (G : ℤ[X][X]) (hG : G ≠ 0) (hY : 0 < degreeY G)
    (hgeom : Geometric G) (x : Pair) (hx : x 1 ≠ 0) : fibre G x ≠ 0 := by
  classical
  let P := PaperP1.RationalBivariateIrreducibility.rationalize G
  have hP : Irreducible P := ScalarIrreducibilityReflection.geometric_rational_irreducible G hG hgeom
  have hdeg : 0 < P.natDegree := (PaperP1.RationalizedCriticalPointBound.outer_degree G).symm ▸ hY
  let p := P.map (Polynomial.evalRingHom (ratio x))
  have hp : p ≠ 0 := RationalCurveCriticalPoints.specialization_nonzero P hP hdeg (ratio x)
  intro hz
  have hzero (n : ℕ) : p.eval (n : ℚ) = 0 := by
    let y : Pair := ![(n : ℤ), 1]
    have he : MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) = 0 := by
      rw [← fibre_evaluation, hz, map_zero]
    have hy : y 1 ≠ 0 := by simp [y]
    have ha := (NonGeometricRationalSingularity.projective_zero_iff G x y hx hy).mp he
    have hb : P.evalEval (ratio x) (n : ℚ) = 0 := by simpa [P, ratio, y] using ha
    simpa only [p, Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hb
  let T := (Finset.range (p.natDegree + 1)).image (fun n : ℕ ↦ (n : ℚ))
  have hsub : T ⊆ p.roots.toFinset := by
    intro z hzT
    obtain ⟨n, _hn, rfl⟩ := mem_image.mp hzT
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hzero n))
  have hcard : T.card = p.natDegree + 1 := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hb : T.card ≤ p.natDegree :=
    (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
  omega

theorem fibre_nonzero (G : ℤ[X][X]) (hG : G ≠ 0) (hY : 0 < degreeY G) (hgeom : Geometric G)
    (x : Pair) (hprim : (x 0).natAbs.Coprime (x 1).natAbs) : fibre G x ≠ 0 := by
  by_cases hx : x 1 = 0
  · have hx₀ : x 0 ≠ 0 := by
      intro hz
      have he := hprim.gcd_eq_one
      rw [hz, hx] at he
      norm_num at he
    exact fibre_axis_nonzero G hG x hx₀ hx
  · exact fibre_nonaxis_nonzero G hG hY hgeom x hx

theorem primitive_fibre_card (G : ℤ[X][X]) (hG : G ≠ 0) (hY : 0 < degreeY G)
    (hgeom : Geometric G) (x : Pair) (hx : (x 0).natAbs.Coprime (x 1).natAbs)
    (S : Finset Pair) (hprim : ∀ y ∈ S, (y 0).natAbs.Coprime (y 1).natAbs)
    (hzero : ∀ y ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) = 0) :
    S.card ≤ 2 * (degreeY G + 1) := by
  apply PrimitiveHomogeneousZeros.primitive_card (fibre G x) (fibre_homogeneous G x)
    (fibre_nonzero G hG hY hgeom x hx) S hprim
  intro y hy
  rw [fibre_evaluation]
  exact hzero y hy

end PaperP1.GeometricProjectiveFibres
