module

public import PaperP1.Algebra.FieldExtensionPolynomialIrreducibility
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Lean.Elab.Tactic.Omega

/-! # Geometric irreducibility gives the actual rational hypersurface prime, positive degree and point evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HypersurfaceRationalData

open MvPolynomial

variable (I : Ideal (MvPolynomial (Fin 4) ℚ)) (q : MvPolynomial (Fin 4) ℚ)
  (hspan : I = Ideal.span {q}) (hgeom : Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q))

include hgeom in
theorem irreducible : Irreducible q :=
  FieldExtensionPolynomialIrreducibility.irreducible_of_map (algebraMap ℚ (AlgebraicClosure ℚ)) q hgeom

include hspan hgeom in
theorem prime : I.IsPrime := by
  rw [hspan]
  exact FieldExtensionPolynomialIrreducibility.prime_span_of_irreducible_map (algebraMap ℚ (AlgebraicClosure ℚ)) q hgeom

include hgeom in
theorem degree_pos (d : ℕ) (hdegree : q.totalDegree = d) : 0 < d := by
  have hirr := irreducible q hgeom
  by_contra hn
  have hd : d = 0 := Nat.eq_zero_of_not_pos hn
  have hzero : q.totalDegree = 0 := hdegree.trans hd
  have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
  have hc : q.coeff 0 ≠ 0 := by
    intro hz
    apply hirr.ne_zero
    rw [he, hz, map_zero]
  apply hirr.not_isUnit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

include hspan in
theorem ideal_le_kernel (v : Fin 4 → ℚ) (hv : eval v q = 0) : I ≤ RingHom.ker (aeval v).toRingHom := by
  rw [hspan]
  exact (Ideal.span_singleton_le_iff_mem _).mpr hv

def evaluation (v : Fin 4 → ℚ) (hv : eval v q = 0) : (MvPolynomial (Fin 4) ℚ ⧸ I) →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ I (aeval v) (ideal_le_kernel I q hspan v hv)

theorem evaluation_mk (v : Fin 4 → ℚ) (hv : eval v q = 0) (P : MvPolynomial (Fin 4) ℚ) :
    evaluation I q hspan v hv (Ideal.Quotient.mk I P) = eval v P := rfl

end PaperP1.P3HypersurfaceRationalData
