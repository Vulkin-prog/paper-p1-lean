module

public import PaperP1.Algebra.ConicCoordinateChanges
public import PaperP1.Algebra.GeometricBiformDegrees
public import PaperP1.Algebra.BoundedPlaneShear

/-! # Geometric irreducibility discharges the conic non-degeneracy conditions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConicIrreducibility

open Polynomial PaperP1.ConicNormCoordinates PaperP1.ConicPolynomialPresentation
open PaperP1.ConicCoordinateChanges PaperP1.GeometricFactorSwap

def form {R : Type*} [CommRing R] (a b c d e f : R) : R[X][X] :=
  C (C a) * C X ^ 2 + C (C b) * C X * X + C (C c) * X ^ 2 +
    C (C d) * C X + C (C e) * X + C (C f)

def square {R : Type*} [CommRing R] (b c e : R) : R[X][X] :=
  C (C (2 * c)) * X + C (C b) * C X + C (C e)

def first {R : Type*} [CommRing R] (Δ β : R) : R[X][X] :=
  C (C (2 * Δ)) * C X + C (C β)

theorem square_identity {R : Type*} [CommRing R] (a b c d e f : R) :
    square b c e ^ 2 = C (C (b ^ 2 - 4 * a * c)) * C X ^ 2 +
      C (C (2 * b * e - 4 * c * d)) * C X + C (C (e ^ 2 - 4 * c * f)) +
        C (C (4 * c)) * form a b c d e f := by
  simp only [square, form, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem norm_identity {R : Type*} [CommRing R] (a b c d e f : R) :
    first (b ^ 2 - 4 * a * c) (2 * b * e - 4 * c * d) ^ 2 -
      C (C (b ^ 2 - 4 * a * c)) * (2 * square b c e) ^ 2 =
        C (C ((2 * b * e - 4 * c * d) ^ 2 - 4 * (b ^ 2 - 4 * a * c) * (e ^ 2 - 4 * c * f))) -
          C (C (16 * c * (b ^ 2 - 4 * a * c))) * form a b c d e f := by
  simp only [first, square, form, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem coefficient_map_form {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b c d e f : R) :
    IntegerCurveRationalization.coefficientMap φ (form a b c d e f) =
      form (φ a) (φ b) (φ c) (φ d) (φ e) (φ f) := by
  simp [form, IntegerCurveRationalization.coefficientMap, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow]

theorem integer_form (Q : Coefficients) : polynomial Q = form Q.a Q.b Q.c Q.d Q.e Q.f :=
  polynomial_expression Q

theorem complex_form (Q : Coefficients) :
    ComplexProjectiveIrreducibility.complexAffine (polynomial Q) =
      form (Q.a : ℂ) (Q.b : ℂ) (Q.c : ℂ) (Q.d : ℂ) (Q.e : ℂ) (Q.f : ℂ) := by
  rw [integer_form]
  exact coefficient_map_form (Int.castRingHom ℂ) Q.a Q.b Q.c Q.d Q.e Q.f

theorem not_isUnit_of_outer_coefficient {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X][X]) (hP : (P.coeff 1).coeff 0 ≠ 0) : ¬IsUnit P := by
  intro hu
  have hd := IntegerCurveRationalization.degree_of_isUnit P hu
  have hout := BivariateResultantDegree.outer_degree_le P
  have hrow : P.coeff 1 ≠ 0 := by intro hz; exact hP (by rw [hz, Polynomial.coeff_zero])
  have hh := Polynomial.le_natDegree_of_ne_zero hrow
  omega

theorem irreducible_normConstant_ne_zero {F : Type*} [Field F] [CharZero F] [IsAlgClosed F]
    (a b c d e f : F) (hc : c ≠ 0) (hP : Irreducible (form a b c d e f)) :
    (2 * b * e - 4 * c * d) ^ 2 - 4 * (b ^ 2 - 4 * a * c) * (e ^ 2 - 4 * c * f) ≠ 0 := by
  let Δ := b ^ 2 - 4 * a * c
  let β := 2 * b * e - 4 * c * d
  let γ := e ^ 2 - 4 * c * f
  let W := square b c e
  have impossible (A B : F[X][X]) (s : F) (hs : s ≠ 0)
      (hfact : A * B = C (C s) * form a b c d e f)
      (hA : (A.coeff 1).coeff 0 ≠ 0) (hB : (B.coeff 1).coeff 0 ≠ 0) : False := by
    have hu : IsUnit (C (C s) : F[X][X]) :=
      Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hs))
    have hp : Irreducible (A * B) := by
      rw [hfact]
      exact (associated_unit_mul_right (form a b c d e f) _ hu).irreducible hP
    rcases hp.2 rfl with hunit | hunit
    · exact not_isUnit_of_outer_coefficient A hA hunit
    · exact not_isUnit_of_outer_coefficient B hB hunit
  intro hδ
  change β ^ 2 - 4 * Δ * γ = 0 at hδ
  by_cases hΔ : Δ = 0
  · have hβ : β = 0 := by
      have hh : β ^ 2 = 0 := by simpa only [hΔ, mul_zero, zero_mul, sub_zero] using hδ
      exact sq_eq_zero_iff.mp hh
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq γ (by decide : 0 < (2 : ℕ))
    have hroot : (C (C r) : F[X][X]) ^ 2 = C (C γ) := by rw [← map_pow, ← map_pow, hr]
    have hW : W ^ 2 = C (C γ) + C (C (4 * c)) * form a b c d e f := by
      have hh := square_identity a b c d e f
      change W ^ 2 = C (C Δ) * C X ^ 2 + C (C β) * C X + C (C γ) +
        C (C (4 * c)) * form a b c d e f at hh
      simpa only [hΔ, hβ, map_zero, zero_mul, zero_add] using hh
    have hfact : (W - C (C r)) * (W + C (C r)) = C (C (4 * c)) * form a b c d e f := by
      calc
        _ = W ^ 2 - C (C r) ^ 2 := by ring
        _ = _ := by rw [hroot, hW]; ring
    have hA : (((W - C (C r)).coeff 1).coeff 0) = 2 * c := by
      norm_num [W, square, Polynomial.coeff_C_mul]
    have hB : (((W + C (C r)).coeff 1).coeff 0) = 2 * c := by
      norm_num [W, square, Polynomial.coeff_C_mul]
    exact impossible _ _ (4 * c) (mul_ne_zero (by norm_num) hc) hfact
      (by rw [hA]; exact mul_ne_zero (by norm_num) hc)
      (by rw [hB]; exact mul_ne_zero (by norm_num) hc)
  · obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq Δ (by decide : 0 < (2 : ℕ))
    have hrne : r ≠ 0 := by intro hz; apply hΔ; rw [← hr, hz, zero_pow (by decide : 2 ≠ 0)]
    let U := first Δ β
    have hroot : (C (C r) : F[X][X]) ^ 2 = C (C Δ) := by rw [← map_pow, ← map_pow, hr]
    have hn : U ^ 2 - C (C Δ) * (2 * W) ^ 2 =
        -(C (C (16 * c * Δ)) * form a b c d e f) := by
      have hh := norm_identity a b c d e f
      change U ^ 2 - C (C Δ) * (2 * W) ^ 2 =
        C (C (β ^ 2 - 4 * Δ * γ)) - C (C (16 * c * Δ)) * form a b c d e f at hh
      simpa only [hδ, map_zero, zero_sub] using hh
    have hfact : (U - C (C r) * (2 * W)) * (U + C (C r) * (2 * W)) =
        C (C (-(16 * c * Δ))) * form a b c d e f := by
      calc
        _ = U ^ 2 - C (C r) ^ 2 * (2 * W) ^ 2 := by ring
        _ = -(C (C (16 * c * Δ)) * form a b c d e f) := by rw [hroot]; exact hn
        _ = _ := by simp only [map_neg]; ring
    have hA : (((U - C (C r) * (2 * W)).coeff 1).coeff 0) = -(4 * r * c) := by
      norm_num [U, W, first, square, Polynomial.coeff_C_mul]
      ring
    have hB : (((U + C (C r) * (2 * W)).coeff 1).coeff 0) = 4 * r * c := by
      norm_num [U, W, first, square, Polynomial.coeff_C_mul]
      ring
    have hrc : 4 * r * c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hrne) hc
    exact impossible _ _ (-(16 * c * Δ))
      (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hc) hΔ)) hfact
      (by rw [hA]; exact neg_ne_zero.mpr hrc) (by rw [hB]; exact hrc)

theorem geometric_normConstant_ne_zero (Q : Coefficients) (hc : Q.c ≠ 0)
    (hgeo : Geometric (polynomial Q)) : normConstant Q ≠ 0 := by
  have hne : polynomial Q ≠ 0 := by
    intro hz
    have he := congrArg (fun P : ℤ[X][X] ↦ (coefficients P).c) hz
    rw [coefficients_polynomial] at he
    exact hc he
  have hP := (HomogenizationIrreducibilityReflection.geometric_iff_affine (polynomial Q) hne).mp hgeo
  rw [complex_form] at hP
  have hcC : (Q.c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hnonzero := irreducible_normConstant_ne_zero (Q.a : ℂ) Q.b Q.c Q.d Q.e Q.f hcC hP
  intro hz
  apply hnonzero
  have hh : (normConstant Q : ℂ) = 0 := by exact_mod_cast hz
  simpa only [normConstant, linear, discriminant, constant, Int.cast_sub, Int.cast_mul,
    Int.cast_pow, Int.cast_ofNat] using hh

theorem grid_normConstant_ne_zero (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P ≤ 2)
    (hout : P.natDegree = 2) (hgeo : Geometric P) : normConstant (coefficients P) ≠ 0 := by
  apply geometric_normConstant_ne_zero (coefficients P) (outer_coefficient_ne_zero P hD hout)
  rwa [reconstruction P hD]

theorem geometric_determinant_ne_zero (P : ℤ[X][X]) (hD : PlaneCurvePointCount.degree P = 2)
    (hgeo : Geometric P) : determinant (coefficients P) ≠ 0 := by
  have hne : P ≠ 0 := by intro hz; simp [PlaneCurvePointCount.degree, hz] at hD
  obtain ⟨t, _ht, hout⟩ := BoundedPlaneShear.exists_full_outer_degree P hne
  rw [hD] at hout
  have hdegree : PlaneCurvePointCount.degree (BivariateLinearShear.shear (t : ℤ) P) = 2 :=
    (BivariateLinearShear.shear_degree _ P).trans hD
  have hgeo' := IntegerPlaneShear.geometric (t : ℤ) P hne hgeo
  have hn := grid_normConstant_ne_zero _ hdegree.le hout hgeo'
  rw [normConstant_determinant, determinant_shear P hD.le] at hn
  intro hz
  exact hn (by rw [hz, mul_zero])

end PaperP1.ConicIrreducibility
