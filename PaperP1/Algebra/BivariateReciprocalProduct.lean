module

public import PaperP1.Algebra.BivariateReciprocalSeries
public import PaperP1.Arithmetic.BiquadraticCoefficientPolynomials
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Multiplication of actual reciprocal bivariate polynomials -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateReciprocalProduct

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateReciprocalSeries
  PaperP1.BiquadraticFormalNumerator PaperP1.BiquadraticCoefficientPolynomials

theorem series_monomial {R : Type*} [CommSemiring R] (n : ℕ) (c : R) :
    PowerSeries.monomial n c = PowerSeries.C c * (PowerSeries.X : PowerSeries R) ^ n := by
  rw [PowerSeries.X_pow_eq, ← PowerSeries.monomial_zero_eq_C_apply,
    PowerSeries.monomial_mul_monomial, zero_add, mul_one]

theorem iterated_monomial (a b : ℕ) (c : ℚ) :
    (IteratedPowerSeriesEquiv.equiv (σ := Unit) (R := ℚ))
        (MvPowerSeries.monomial (BivariateSeriesOrder.exponent a b) c) =
      PowerSeries.C (PowerSeries.C c) *
        (PowerSeries.C (PowerSeries.X : PowerSeries ℚ) ^ a * (PowerSeries.X : Series) ^ b) := by
  change IteratedPowerSeriesEquiv.toIterated
    (MvPowerSeries.monomial (BivariateSeriesOrder.exponent a b) c) = _
  rw [IteratedPowerSeriesEquiv.toIterated_monomial]
  have he : (BivariateSeriesOrder.exponent a b).some = Finsupp.single () a := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  rw [BivariateSeriesOrder.exponent_outer, he]
  change PowerSeries.monomial b (PowerSeries.monomial a c) = _
  rw [series_monomial, series_monomial, map_mul, map_pow]
  ring

theorem reciprocal_sum (P : ℤ[X][X]) (a b : ℕ) :
    reciprocal P a b = ∑ i : Fin (a + 1) × Fin (b + 1),
      PowerSeries.C (PowerSeries.C ((P.coeff i.2.val).coeff i.1.val : ℚ)) *
        (PowerSeries.C (PowerSeries.X : PowerSeries ℚ) ^ (a - i.1.val) *
          (PowerSeries.X : Series) ^ (b - i.2.val)) := by
  unfold reciprocal reciprocalMulti
  rw [map_sum]
  exact sum_congr rfl (fun i _ ↦ iterated_monomial _ _ _)

theorem row_reconstruction (p : ℤ[X]) (m : ℕ) (hp : p.natDegree ≤ m) :
    row m (fun i ↦ p.coeff i.val) = p := by
  apply Polynomial.ext
  intro i
  by_cases hi : i ≤ m
  · exact row_coefficient m _ ⟨i, by omega⟩
  · rw [coeff_eq_zero_of_natDegree_lt ((row_degree m _).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega))]

theorem rectangle_reconstruction (P : ℤ[X][X]) (a b : ℕ)
    (hx : degreeX P ≤ a) (hy : degreeY P ≤ b) :
    rectangle a b (fun i ↦ (P.coeff i.2.val).coeff i.1.val) = P := by
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ b
  · rw [show j = (⟨j, by omega⟩ : Fin (b + 1)).val from rfl,
      rectangle_outer_coefficient]
    exact row_reconstruction _ _ ((natDegree_coeff_le_degreeX P j).trans hx)
  · rw [coeff_eq_zero_of_natDegree_lt ((rectangle_degreeY a b _).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt (hy.trans_lt (by omega))]

abbrev SeriesField := FractionRing Series

def embed : Series →+* SeriesField := algebraMap Series SeriesField

theorem embed_injective : Function.Injective embed := IsFractionRing.injective Series SeriesField

def x : SeriesField := embed (PowerSeries.C (PowerSeries.X : PowerSeries ℚ))

def y : SeriesField := embed (PowerSeries.X : Series)

theorem x_ne_zero : x ≠ 0 := by
  intro h
  apply PowerSeries.X_ne_zero (R := ℚ)
  apply PowerSeries.C_injective
  apply embed_injective
  simpa only [x, map_zero] using h

theorem y_ne_zero : y ≠ 0 := by
  intro h
  apply PowerSeries.X_ne_zero (R := PowerSeries ℚ)
  apply embed_injective
  simpa only [y, map_zero] using h

def evaluateInverse : ℤ[X][X] →+* SeriesField :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom SeriesField) x⁻¹) y⁻¹

theorem reverse_power {F : Type*} [Field F] (z : F) (hz : z ≠ 0) (a i : ℕ) (hi : i ≤ a) :
    z ^ a * (z⁻¹) ^ i = z ^ (a - i) := by
  conv_lhs => rw [← Nat.sub_add_cancel hi, pow_add]
  rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]

theorem embed_scalar (c : ℤ) :
    embed (PowerSeries.C (PowerSeries.C (c : ℚ))) = (c : SeriesField) := by
  simp only [map_intCast]

theorem evaluate_rectangle (a b : ℕ) (w : Fin (a + 1) × Fin (b + 1) → ℤ) :
    evaluateInverse (rectangle a b w) =
      ∑ i : Fin (a + 1) × Fin (b + 1), (w i : SeriesField) * (x⁻¹) ^ i.1.val * (y⁻¹) ^ i.2.val := by
  unfold evaluateInverse rectangle row
  simp only [map_sum, coe_eval₂RingHom, eval₂_monomial,
    Int.coe_castRingHom, Fintype.sum_prod_type]
  exact sum_comm

theorem embed_reciprocal (P : ℤ[X][X]) (a b : ℕ)
    (hx : degreeX P ≤ a) (hy : degreeY P ≤ b) :
    embed (reciprocal P a b) = x ^ a * y ^ b * evaluateInverse P := by
  have he : evaluateInverse P = ∑ i : Fin (a + 1) × Fin (b + 1),
      ((P.coeff i.2.val).coeff i.1.val : SeriesField) * (x⁻¹) ^ i.1.val * (y⁻¹) ^ i.2.val := by
    conv_lhs => rw [← rectangle_reconstruction P a b hx hy]
    exact evaluate_rectangle a b _
  rw [reciprocal_sum, map_sum, he, mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [map_mul, map_pow, embed_scalar]
  change ((P.coeff i.2.val).coeff i.1.val : SeriesField) *
    (x ^ (a - i.1.val) * y ^ (b - i.2.val)) = _
  have hxi := reverse_power x x_ne_zero a i.1.val (by omega)
  have hyi := reverse_power y y_ne_zero b i.2.val (by omega)
  rw [← hxi, ← hyi]
  ring

theorem reciprocal_mul (P Q : ℤ[X][X]) (a b c d : ℕ)
    (hPx : degreeX P ≤ a) (hPy : degreeY P ≤ b)
    (hQx : degreeX Q ≤ c) (hQy : degreeY Q ≤ d) :
    reciprocal (P * Q) (a + c) (b + d) = reciprocal P a b * reciprocal Q c d := by
  have hx : degreeX (P * Q) ≤ a + c := by
    change (Bivariate.swap (P * Q)).natDegree ≤ a + c
    rw [map_mul]
    exact natDegree_mul_le.trans (add_le_add hPx hQx)
  have hy : degreeY (P * Q) ≤ b + d := natDegree_mul_le.trans (add_le_add hPy hQy)
  apply embed_injective
  rw [map_mul, embed_reciprocal (P * Q) _ _ hx hy,
    embed_reciprocal P _ _ hPx hPy, embed_reciprocal Q _ _ hQx hQy, map_mul, pow_add, pow_add]
  ring

end PaperP1.BivariateReciprocalProduct
