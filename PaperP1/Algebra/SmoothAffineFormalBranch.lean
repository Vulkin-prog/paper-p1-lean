module

public import PaperP1.Algebra.PowerSeriesSimpleRoot
public import PaperP1.Algebra.RationalCurveCriticalPoints
public import Mathlib.Algebra.Polynomial.Taylor

/-! # A formal branch at every affine point with nonzero outer derivative

The selected point may be any field-valued point. No leading coefficient,
integer first coordinate or globally regular fibre condition is required.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothAffineFormalBranch

open Polynomial

variable {F : Type*} [Field F]

def xSeries (x : F) : PowerSeries F := PowerSeries.X + PowerSeries.C x

def coefficientLift (x : F) : F[X] →+* PowerSeries F :=
  Polynomial.eval₂RingHom PowerSeries.C (xSeries x)

def curvePolynomial (P : F[X][X]) (x : F) : (PowerSeries F)[X] :=
  P.map (coefficientLift x)

def evaluation (x : F) (y : PowerSeries F) : F[X][X] →+* PowerSeries F :=
  Polynomial.eval₂RingHom (coefficientLift x) y

theorem coefficientLift_constant (x : F) :
    PowerSeries.constantCoeff.comp (coefficientLift x) = Polynomial.evalRingHom x := by
  ext <;> simp [coefficientLift, xSeries]

theorem curvePolynomial_constant (P : F[X][X]) (x : F) :
    (curvePolynomial P x).map PowerSeries.constantCoeff = P.map (Polynomial.evalRingHom x) := by
  rw [curvePolynomial, Polynomial.map_map, coefficientLift_constant]

theorem coefficientLift_injective (x : F) : Function.Injective (coefficientLift x) := by
  have he : coefficientLift x =
      (Polynomial.coeToPowerSeries.ringHom : F[X] →+* PowerSeries F).comp
        (Polynomial.taylorEquiv x).toRingHom := by
    ext <;> simp [coefficientLift, xSeries, Polynomial.taylorEquiv, Polynomial.taylor_X]
  rw [he]
  exact (Polynomial.coe_injective F).comp (Polynomial.taylorEquiv x).injective

theorem exists_branch (P : F[X][X]) (x z : F)
    (hz : P.evalEval x z = 0) (hd : P.derivative.evalEval x z ≠ 0) :
    ∃ y : PowerSeries F, PowerSeries.constantCoeff y = z ∧ evaluation x y P = 0 := by
  have hr : ((curvePolynomial P x).map PowerSeries.constantCoeff).eval z = 0 := by
    rw [curvePolynomial_constant, Polynomial.map_evalRingHom_eval]
    exact hz
  have hdr : ((curvePolynomial P x).map PowerSeries.constantCoeff).derivative.eval z ≠ 0 := by
    rw [curvePolynomial_constant, Polynomial.derivative_map, Polynomial.map_evalRingHom_eval]
    exact hd
  obtain ⟨y, hy, hcy⟩ := PaperP1.PowerSeriesSimpleRoot.exists_root (curvePolynomial P x) z hr hdr
  refine ⟨y, hcy, ?_⟩
  exact (Polynomial.eval₂_eq_eval_map (coefficientLift x)).trans hy

theorem evaluation_zero_iff (P : F[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (x : F) (y : PowerSeries F) (hy : evaluation x y P = 0)
    (Q : F[X][X]) : evaluation x y Q = 0 ↔ P ∣ Q := by
  constructor
  · intro hQ
    by_contra hn
    have hres := PaperP1.RationalCurveCriticalPoints.resultant_nonzero_of_not_dvd P Q hP hdeg hn
    obtain ⟨a, b, _ha, _hb, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      P Q le_rfl le_rfl (Or.inl (ne_of_gt hdeg))
    have h := congrArg (evaluation x y) hbez
    have hzero : coefficientLift x (P.resultant Q) = 0 := by
      have hh : evaluation x y (C (P.resultant Q)) = 0 := by
        simpa only [map_add, map_mul, hy, hQ, zero_mul, zero_add] using h.symm
      simpa only [evaluation, coe_eval₂RingHom, Polynomial.eval₂_C] using hh
    exact hres ((coefficientLift_injective x) (hzero.trans (map_zero (coefficientLift x)).symm))
  · rintro ⟨Q, rfl⟩
    rw [map_mul, hy, zero_mul]

end PaperP1.SmoothAffineFormalBranch
