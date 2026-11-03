module

public import PaperP1.Algebra.CommonQuotientGraph
public import Mathlib.RingTheory.Ideal.Maps

/-! # A function-field graph relation specializes at every actual point of its coordinate ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BivariateGraphSpecialization

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def relation (p q : F[X]) : F[X][X] := C p - X * C q

theorem relation_evaluation (x y : E) (p q : F[X]) :
    Polynomial.aevalAeval x y (relation p q) = aeval x p - y * aeval x q := by
  simp only [relation, map_sub, map_mul, Polynomial.aevalAeval_C, Polynomial.aevalAeval_Y]

theorem relation_mem_kernel (x y : E) (p q : F[X])
    (hgraph : aeval x p = y * aeval x q) :
    relation p q ∈ RingHom.ker (Polynomial.aevalAeval x y).toRingHom := by
  exact RingHom.mem_ker.mpr ((relation_evaluation x y p q).trans (sub_eq_zero.mpr hgraph))

theorem point_equation (x y : E) (X Y : F) (p q : F[X])
    (hgraph : aeval x p = y * aeval x q)
    (hpoint : RingHom.ker (Polynomial.aevalAeval (R := F) x y).toRingHom ≤
      RingHom.ker (Polynomial.aevalAeval (R := F) X Y).toRingHom) :
    p.eval X = Y * q.eval X := by
  have hzero := RingHom.mem_ker.mp (hpoint (relation_mem_kernel x y p q hgraph))
  change Polynomial.aevalAeval X Y (relation p q) = 0 at hzero
  rw [relation_evaluation] at hzero
  exact sub_eq_zero.mp hzero

end PaperP1.BivariateGraphSpecialization
