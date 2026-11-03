module

public import PaperP1.Algebra.AffineLineClassification
public import PaperP1.Algebra.HomogeneousAffinePrincipalChart
public import PaperP1.Algebra.HomogeneousAffineDegree

/-! # An actual affine host supplies the nonempty chart and the actual irreducible bounded-degree affine image equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveHostChart

open Polynomial PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.StandardVeroneseCoordinates PaperP1.NativeVeroneseAffineIdeal

variable {F : Type*} [Field F] (D : ℕ) (Q : Ideal (Base F D)) (x y : F)
  (hhost : affineIdeal F D Q ≤ RingHom.ker (AffineLineClassification.valueMap x y))

include hhost in
theorem coordinate_ne_zero : Ideal.Quotient.mk Q (coordinatePower F D 2) ≠ 0 := by
  intro hz
  have hm := Ideal.mem_map_of_mem (affineMap F D) (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have he : affineMap F D (coordinatePower F D 2) = 1 := by
    rw [affineMap_apply, coordinatePower_val, map_pow, specialization_Z, one_pow]
  have hzero := RingHom.mem_ker.mp (hhost (he ▸ hm))
  exact one_ne_zero (by simpa only [map_one] using hzero)

include hhost in
theorem not_infinity (f : MvPolynomial (Fin 3) F) (hD : 0 < D)
    (hbase : Q = PlaneCurveVeroneseBaseQuotient.ideal F f D) :
    MvPolynomial.X (2 : Fin 3) ∉ HomogeneousPrincipalQuotient.ideal f := by
  intro hz
  have hpow : MvPolynomial.X (2 : Fin 3) ^ D ∈ HomogeneousPrincipalQuotient.ideal f := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    rw [pow_succ]
    exact Ideal.mul_mem_left _ _ hz
  have hmem : coordinatePower F D 2 ∈ Q := by rw [hbase]; exact hpow
  exact coordinate_ne_zero D Q x y hhost (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

include hhost in
theorem affine_point {e : ℕ} (f : MvPolynomial (Fin 3) F) (hf : f.IsHomogeneous e) (hD : 0 < D)
    (hbase : Q = PlaneCurveVeroneseBaseQuotient.ideal F f D) :
    (NativeAffineChart.specialization F f).evalEval x y = 0 := by
  have himage := (congrArg (affineIdeal F D) hbase).trans (contracted_principal f hf D hD)
  have hm : NativeAffineChart.specialization F f ∈ affineIdeal F D Q :=
    himage.symm ▸ Ideal.mem_span_singleton_self _
  have hz := RingHom.mem_ker.mp (hhost hm)
  have he : (NativeAffineChart.specialization F f).evalEval x y =
      AffineLineClassification.valueMap x y (NativeAffineChart.specialization F f) :=
    congrArg (fun φ : F[X][X] →+* F ↦ φ (NativeAffineChart.specialization F f))
      (congrFun (Polynomial.evalEvalRingHom_eq x) y)
  exact he.trans hz

end PaperP1.SourceCurveHostChart
