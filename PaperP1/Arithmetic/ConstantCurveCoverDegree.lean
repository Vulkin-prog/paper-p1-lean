module

public import PaperP1.Algebra.IntegerConstantCurve
public import PaperP1.Algebra.UnivariateRadicalCoverDegree
public import PaperP1.Arithmetic.ScaledCurveEquationClasses

/-! # Literal radical covers over constant-coordinate integer curves have exponential degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConstantCurveCoverDegree

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveFunctionField
  PaperP1.FormalWordPolynomials PaperP1.IntegerConstantCurve

theorem vertical_word (x d : ℤ) (I J : Finset ℤ) :
    verticalMap x (ScaledCurveSquareMatching.word d I J) =
      C (d * (linearOver ℤ I).eval x) * linearOver ℤ J := by
  have he : (evalRingHom x).comp (C : ℤ →+* ℤ[X]) = RingHom.id ℤ := by
    ext a
    exact eval_C
  change (C (C d) * (C (linearOver ℤ I) * (linearOver ℤ J).map C)).map (evalRingHom x) = _
  simp only [Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom, eval_C,
    Polynomial.map_map, he, Polynomial.map_id, map_mul]
  ring

theorem horizontal_word (y d : ℤ) (I J : Finset ℤ) :
    horizontalMap y (ScaledCurveSquareMatching.word d I J) =
      C (d * (linearOver ℤ J).eval y) * linearOver ℤ I := by
  change (C (C d) * (C (linearOver ℤ I) * (linearOver ℤ J).map C)).eval (C y) = _
  simp only [eval_mul, eval_C, eval_map]
  change C d * (linearOver ℤ I * (linearOver ℤ J).comp (C y)) = _
  rw [comp_C]
  simp only [map_mul]
  ring

theorem eval_ne_zero (x : ℤ) (I : Finset ℤ) (hpos : ∀ z ∈ I, 0 < x + z) :
    (linearOver ℤ I).eval x ≠ 0 := by
  simp only [linearOver, eval_prod, eval_add, eval_X, eval_C, Int.cast_id]
  exact prod_ne_zero_iff.mpr (fun z hz ↦ (hpos z hz).ne')

variable {ι : Type*} [Fintype ι] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
  (d : ι → ℤ) (hd : ∀ ν, d ν ≠ 0) (I J : ι → Finset ℤ)
  {L : Type*} [Field L] [Algebra (FunctionField C₀) L]

include hd in
theorem vertical_power_dvd_degree (x y : ℤ) (hY : degreeY C₀ = 0)
    (hpoint : C₀.evalEval x y = 0) (hpos : ∀ ν, ∀ z ∈ I ν, 0 < x + z)
    (hne : ∀ ν, (J ν).Nonempty) (hJ : Pairwise fun ν μ ↦ Disjoint (J ν) (J μ))
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I J ν)) :
    2 ^ Fintype.card ι ∣ Module.finrank (FunctionField C₀) L := by
  let e := functionEquiv C₀ (verticalMap x) (ideal_vertical C₀ x y hY hpoint) (verticalMap_surjective x)
  let c : ι → ℤ := fun ν ↦ d ν * (linearOver ℤ (I ν)).eval x
  have hc (ν : ι) : c ν ≠ 0 := mul_ne_zero (hd ν) (eval_ne_zero x (I ν) (hpos ν))
  apply UnivariateRadicalCoverDegree.power_dvd_degree e
    (fun ν ↦ ScaledCurveEquationClasses.value C₀ d I J ν) c hc J hne hJ _ r hr
  intro ν
  change functionEquiv C₀ _ _ _ (specialize C₀ (ScaledCurveSquareMatching.word (d ν) (I ν) (J ν))) = _
  rw [functionEquiv_specialize, vertical_word]
  rfl

include hd in
theorem horizontal_power_dvd_degree (x y : ℤ) (hX : degreeX C₀ = 0)
    (hpoint : C₀.evalEval x y = 0) (hpos : ∀ ν, ∀ z ∈ J ν, 0 < y + z)
    (hne : ∀ ν, (I ν).Nonempty) (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ))
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I J ν)) :
    2 ^ Fintype.card ι ∣ Module.finrank (FunctionField C₀) L := by
  let e := functionEquiv C₀ (horizontalMap y) (ideal_horizontal C₀ x y hX hpoint) (horizontalMap_surjective y)
  let c : ι → ℤ := fun ν ↦ d ν * (linearOver ℤ (J ν)).eval y
  have hc (ν : ι) : c ν ≠ 0 := mul_ne_zero (hd ν) (eval_ne_zero y (J ν) (hpos ν))
  apply UnivariateRadicalCoverDegree.power_dvd_degree e
    (fun ν ↦ ScaledCurveEquationClasses.value C₀ d I J ν) c hc I hne hI _ r hr
  intro ν
  change functionEquiv C₀ _ _ _ (specialize C₀ (ScaledCurveSquareMatching.word (d ν) (I ν) (J ν))) = _
  rw [functionEquiv_specialize, horizontal_word]
  rfl

include hd in
theorem no_vertical_bounded_cover [Module.Finite (FunctionField C₀) L]
    (x y : ℤ) (hY : degreeY C₀ = 0) (hpoint : C₀.evalEval x y = 0)
    (hpos : ∀ ν, ∀ z ∈ I ν, 0 < x + z) (hne : ∀ ν, (J ν).Nonempty)
    (hJ : Pairwise fun ν μ ↦ Disjoint (J ν) (J μ))
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I J ν)) (E : ℕ)
    (hrank : Module.finrank (FunctionField C₀) L ≤ E) (hlarge : E ≤ Fintype.card ι) : False := by
  have hdegree := Nat.le_of_dvd Module.finrank_pos
    (vertical_power_dvd_degree C₀ d hd I J x y hY hpoint hpos hne hJ r hr)
  exact (Fintype.card ι).lt_two_pow_self.not_ge (hdegree.trans (hrank.trans hlarge))

include hd in
theorem no_horizontal_bounded_cover [Module.Finite (FunctionField C₀) L]
    (x y : ℤ) (hX : degreeX C₀ = 0) (hpoint : C₀.evalEval x y = 0)
    (hpos : ∀ ν, ∀ z ∈ J ν, 0 < y + z) (hne : ∀ ν, (I ν).Nonempty)
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ))
    (r : ι → L) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I J ν)) (E : ℕ)
    (hrank : Module.finrank (FunctionField C₀) L ≤ E) (hlarge : E ≤ Fintype.card ι) : False := by
  have hdegree := Nat.le_of_dvd Module.finrank_pos
    (horizontal_power_dvd_degree C₀ d hd I J x y hX hpoint hpos hne hI r hr)
  exact (Fintype.card ι).lt_two_pow_self.not_ge (hdegree.trans (hrank.trans hlarge))

include hd in
theorem partial_degrees_pos [Module.Finite (FunctionField C₀) L] (j : ι → ℤ)
    (x y : ℤ) (hpoint : C₀.evalEval x y = 0)
    (hposX : ∀ ν, ∀ z ∈ I ν, 0 < x + z) (hposY : ∀ ν, 0 < y + j ν)
    (hne : ∀ ν, (I ν).Nonempty) (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ))
    (hj : Function.Injective j) (r : ι → L)
    (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) L
      (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν)) (E : ℕ)
    (hrank : Module.finrank (FunctionField C₀) L ≤ E) (hlarge : E ≤ Fintype.card ι) :
    0 < degreeX C₀ ∧ 0 < degreeY C₀ := by
  have hsingleton : Pairwise fun ν μ ↦ Disjoint ({j ν} : Finset ℤ) {j μ} := by
    intro ν μ hne
    simpa only [Finset.disjoint_singleton] using hj.ne hne
  constructor
  · by_contra hx
    apply no_horizontal_bounded_cover C₀ d hd I (fun μ ↦ {j μ}) x y (by omega) hpoint _ hne hI r hr E hrank hlarge
    intro ν z hz
    exact Finset.mem_singleton.mp hz ▸ hposY ν
  · by_contra hy
    exact no_vertical_bounded_cover C₀ d hd I (fun μ ↦ {j μ}) x y (by omega) hpoint hposX
      (fun _ ↦ Finset.singleton_nonempty _) hsingleton r hr E hrank hlarge

end PaperP1.ConstantCurveCoverDegree
