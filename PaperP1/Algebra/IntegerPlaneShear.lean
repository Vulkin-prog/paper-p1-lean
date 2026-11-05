module

public import PaperP1.Algebra.BivariateLinearShear
public import PaperP1.Algebra.LinearPolynomialHeightTransport
public import PaperP1.Algebra.GeometricBiformDegrees

/-! # Integer plane shears with finite coefficient and point-height budgets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPlaneShear

open Polynomial Finset PaperP1.BivariateLinearShear PaperP1.BivariateTotalDegreeChart
open PaperP1.BivariateHeight PaperP1.GeometricFactorSwap

theorem outer_variable {R : Type*} [CommRing R] (t : R) :
    shear t (Polynomial.X : R[X][X]) = Polynomial.X := by
  have he : shear t (chart R (MvPolynomial.X 0)) = chart R (MvPolynomial.X 0) := by
    change chart R (HomogeneousLinearShear.substitute (fun _ : Fin 1 ↦ t)
      ((chart R).symm (chart R (MvPolynomial.X 0)))) = _
    rw [AlgEquiv.symm_apply_apply]
    simp [HomogeneousLinearShear.substitute]
  simpa only [chart_X_zero] using he

theorem inner_variable {R : Type*} [CommRing R] (t : R) :
    shear t (Polynomial.C (Polynomial.X : R[X])) =
      Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C t) * Polynomial.X := by
  have he : shear t (chart R (MvPolynomial.X 1)) =
      chart R (MvPolynomial.X 1 + MvPolynomial.C t * MvPolynomial.X 0) := by
    change chart R (HomogeneousLinearShear.substitute (fun _ : Fin 1 ↦ t)
      ((chart R).symm (chart R (MvPolynomial.X 1)))) = _
    rw [AlgEquiv.symm_apply_apply]
    simp [HomogeneousLinearShear.substitute]
  have hc : chart R (MvPolynomial.C t) = C (C t) := (chart R).commutes t
  simpa only [map_add, map_mul, chart_X_one, chart_X_zero, hc] using he

theorem scalar {R : Type*} [CommRing R] (t a : R) :
    shear t (Polynomial.C (Polynomial.C a)) = Polynomial.C (Polynomial.C a) :=
  (shear t).commutes a

theorem coefficient_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (t : R) (P : R[X][X]) :
    (shear t P).map (Polynomial.mapRingHom f) =
      shear (f t) (P.map (Polynomial.mapRingHom f)) := by
  let M := Polynomial.mapRingHom (Polynomial.mapRingHom f)
  have he : M.comp (shear t).toRingHom = (shear (f t)).toRingHom.comp M := by
    apply Polynomial.ringHom_ext
    · have hc : (M.comp (shear t).toRingHom).comp Polynomial.C =
          ((shear (f t)).toRingHom.comp M).comp Polynomial.C := by
        apply Polynomial.ringHom_ext
        · intro a
          change M (shear t (C (C a))) = shear (f t) (M (C (C a)))
          simp [M, scalar]
        · change M (shear t (C X)) = shear (f t) (M (C X))
          simp [M, inner_variable]
      intro a
      exact RingHom.congr_fun hc a
    · change M (shear t X) = shear (f t) (M X)
      simp [M, outer_variable]
  exact RingHom.congr_fun he P

theorem geometric (t : ℤ) (P : ℤ[X][X]) (hP : P ≠ 0) (hgeo : Geometric P) :
    Geometric (shear t P) := by
  have hne : shear t P ≠ 0 := (map_ne_zero_iff (shear t) (shear t).injective).mpr hP
  apply (HomogenizationIrreducibilityReflection.geometric_iff_affine _ hne).mpr
  have hi := (HomogenizationIrreducibilityReflection.geometric_iff_affine P hP).mp hgeo
  change Irreducible (complexBivariate P) at hi
  change Irreducible (complexBivariate (shear t P))
  have hm : complexBivariate (shear t P) = shear (t : ℂ) (complexBivariate P) :=
    coefficient_map (Int.castRingHom ℂ) t P
  rw [hm]
  exact (MulEquiv.irreducible_iff (shear (t : ℂ)).toMulEquiv).mpr hi

def point (t : ℤ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1 - t * z.2, z.2)

theorem point_injective (t : ℤ) : Function.Injective (point t) := by
  intro z w he
  have hy := congrArg (fun q : ℤ × ℤ ↦ q.2) he
  change z.2 = w.2 at hy
  have hx : z.1 - t * z.2 = w.1 - t * w.2 := congrArg Prod.fst he
  exact Prod.ext (by rw [hy] at hx; linarith) hy

theorem point_zero (t : ℤ) (P : ℤ[X][X]) (z : ℤ × ℤ) (hz : P.evalEval z.1 z.2 = 0) :
    (shear t P).evalEval (point t z).1 (point t z).2 = 0 := by
  rw [shear_evaluation]
  simpa only [point, sub_add_cancel] using hz

theorem point_box (D t : ℕ) (ht : t ≤ D) (H : ℝ) (hH : 0 ≤ H) (z : ℤ × ℤ)
    (hx : |(z.1 : ℝ)| ≤ H) (hy : |(z.2 : ℝ)| ≤ H) :
    |((point (t : ℤ) z).1 : ℝ)| ≤ ((D : ℝ) + 1) * H ∧
      |((point (t : ℤ) z).2 : ℝ)| ≤ ((D : ℝ) + 1) * H := by
  have htR : (t : ℝ) ≤ D := by exact_mod_cast ht
  have hmul : (t : ℝ) * |(z.2 : ℝ)| ≤ (D : ℝ) * H :=
    mul_le_mul htR hy (abs_nonneg _) (Nat.cast_nonneg _)
  constructor
  · change |((z.1 - (t : ℤ) * z.2 : ℤ) : ℝ)| ≤ _
    push_cast
    have hh := abs_sub (z.1 : ℝ) ((t : ℝ) * z.2)
    have htabs : |(t : ℝ)| = t := abs_of_nonneg (Nat.cast_nonneg t)
    rw [abs_mul, htabs] at hh
    linarith
  · change |(z.2 : ℝ)| ≤ _
    nlinarith [Nat.cast_nonneg (α := ℝ) D]

def heightBudget (D : ℕ) : ℕ :=
  (range (D + 1)).sup (fun t ↦
    LinearPolynomialHeightTransport.budget D (shear (t : ℤ)).toLinearMap)

theorem height_budget (D t : ℕ) (ht : t ≤ D) (P : ℤ[X][X])
    (hD : PlaneCurvePointCount.degree P ≤ D) :
    height (shear (t : ℤ) P) ≤ heightBudget D * height P := by
  exact LinearPolynomialHeightTransport.finite_family_height D (range (D + 1))
    (fun i ↦ (shear (i : ℤ)).toLinearMap) t (mem_range.mpr (by omega)) P hD

end PaperP1.IntegerPlaneShear
