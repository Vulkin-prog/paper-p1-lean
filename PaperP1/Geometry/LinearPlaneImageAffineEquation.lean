module

public import PaperP1.Algebra.MonicPlaneAffineChart
public import PaperP1.Geometry.LinearPlaneMinimalEquation

/-! # The concrete finite plane image has an irreducible monic affine equation of its actual Hilbert degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearPlaneImageAffineEquation

open MvPolynomial LinearPlaneImage

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  [Algebra (MvPolynomial (Fin 2) F) A] [IsScalarTower F (MvPolynomial (Fin 2) F) A]

def equation (y : A) : Polynomial (Polynomial F) :=
  MonicPlaneAffineChart.chart (LinearPlaneMinimalEquation.equation (F := F) y)

omit [Algebra (MvPolynomial (Fin 2) F) A] [IsScalarTower F (MvPolynomial (Fin 2) F) A] in
theorem point_on_chart (g : Fin 2 → A) (y : A) (q : MvPolynomial (Fin 3) F)
    (hq : q ∈ ideal (F := F) g y) (φ : A →ₐ[F] F) (hφ : φ (g 0) = 1) :
    (MonicPlaneAffineChart.chart q).evalEval (φ (g 1)) (φ y) = 0 := by
  rw [MonicPlaneAffineChart.evaluation]
  have hh := congrArg φ (show aeval (coordinates g y) q = 0 from hq)
  rw [map_zero, comp_aeval_apply] at hh
  change eval (fun i ↦ φ (coordinates g y i)) q = 0 at hh
  have hw : (fun i ↦ φ (coordinates g y i)) = ![φ y, 1, φ (g 1)] := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · fin_cases j
      · exact hφ
      · rfl
  rwa [hw] at hh

theorem properties [IsDomain A] (H : ℕ → Submodule F A) [GradedAlgebra H]
    (g : Fin 2 → A) (hg : ∀ i, g i ∈ H 1) (y : A) (hy : y ∈ H 1)
    (hsource : algebraMap (MvPolynomial (Fin 2) F) A = (aeval (R := F) g).toRingHom)
    (hfinite : (aeval (R := F) g).Finite) (hinj : Function.Injective (aeval (R := F) g))
    (d : ℕ) (b : ℚ) (hp : GradedHilbertPolynomial.IsHilbertPolynomial (piece (F := F) g y)
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C b)) :
    Irreducible (equation (F := F) y) ∧ PlaneCurvePointCount.degree (equation (F := F) y) = d ∧
      (equation (F := F) y).Monic ∧ ∀ φ : A →ₐ[F] F, φ (g 0) = 1 →
        (equation (F := F) y).evalEval (φ (g 1)) (φ y) = 0 := by
  have hmapinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) F) A) := by
    rw [hsource]
    exact hinj
  let : FaithfulSMul (MvPolynomial (Fin 2) F) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hmapinj
  let : Module.IsTorsionFree (MvPolynomial (Fin 2) F) A := inferInstance
  have hfin : Module.Finite (MvPolynomial (Fin 2) F) A := by
    apply RingHom.finite_algebraMap.mp
    rw [hsource]
    exact hfinite
  let : Module.Finite (MvPolynomial (Fin 2) F) A := hfin
  have hint : IsIntegral (MvPolynomial (Fin 2) F) y := IsIntegral.of_finite _ y
  let q := LinearPlaneMinimalEquation.equation (F := F) y
  have hq := LinearPlaneMinimalEquation.equation_irreducible g y hsource hint
  have hd := LinearPlaneMinimalEquation.degree_of_image_hilbert H g hg y hy hsource hint d b hp
  have hhom : q.IsHomogeneous d := by
    have hh := LinearPlaneMinimalEquation.equation_homogeneous H g hg y hy hsource hint
    have he := LinearPlaneMinimalEquation.equation_totalDegree H g hg y hy hsource hint
    rw [← he, hd] at hh
    exact hh
  have hm := LinearPlaneMinimalEquation.equation_monic (F := F) y hint
  have hqI : q ∈ ideal (F := F) g y := by
    rw [LinearPlaneMinimalEquation.principal g y hsource hint]
    exact Ideal.mem_span_singleton_self q
  have hg0 : g 0 ≠ 0 := by
    intro hz
    have he : aeval (R := F) g (X (0 : Fin 2)) = aeval (R := F) g 0 := by
      rw [aeval_X, map_zero]
      exact hz
    exact X_ne_zero (0 : Fin 2) (hinj he)
  have hchart : X (1 : Fin 3) ∉ Ideal.span {q} := by
    intro hh
    rw [← LinearPlaneMinimalEquation.principal g y hsource hint] at hh
    apply hg0
    change aeval (coordinates g y) (X (1 : Fin 3)) = 0 at hh
    rw [aeval_X] at hh
    exact hh
  refine ⟨MonicPlaneAffineChart.irreducible q hq hhom hchart,
    MonicPlaneAffineChart.degree_of_homogeneous_monic q hm hhom,
    MonicPlaneAffineChart.monic q hm, ?_⟩
  intro φ hφ
  exact point_on_chart g y q hqI φ hφ

end PaperP1.LinearPlaneImageAffineEquation
