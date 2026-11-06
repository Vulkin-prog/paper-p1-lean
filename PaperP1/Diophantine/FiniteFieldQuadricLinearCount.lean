module

public import PaperP1.Algebra.FirstChartCoordinateEquiv
public import PaperP1.Algebra.LinearFirstCoordinateNormalization
public import PaperP1.Algebra.CoordinateSwapEvaluation

/-! # Direct finite-field counting for irreducible quadrics with a nonzero actual linear part -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldQuadricLinearCount

open MvPolynomial Finset
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem first_coefficient_bound (L Q : MvPolynomial (Fin 3) F)
    (hL : L.IsHomogeneous 1) (hQ : Q.IsHomogeneous 2)
    (ha : L.coeff (Finsupp.single 0 1) ≠ 0)
    (hirr : Irreducible (QuadricNormalHomogenization.polynomial L Q))
    (S : Finset (Fin 3 → F)) (hS : ∀ v ∈ S, eval v L + eval v Q = 0) :
    S.card ≤ Fintype.card F ^ 2 + 2 * Fintype.card F := by
  obtain ⟨b, hb⟩ := LinearFirstCoordinateNormalization.normalize L hL ha
  let a := L.coeff (Finsupp.single 0 1)
  let Q' := FirstCoordinateShear.substitute b Q
  have hQ' : Q'.IsHomogeneous 2 := FirstCoordinateShear.homogeneous b Q hQ
  have hi : Irreducible (QuadricNormalHomogenization.polynomial (C a * X 0) Q') := by
    have hh := (MulEquiv.irreducible_iff
      (FirstChartCoordinateEquiv.liftEquiv (FirstCoordinateShear.equiv b)).toMulEquiv).mpr hirr
    change Irreducible (FirstChartCoordinateEquiv.liftEquiv (FirstCoordinateShear.equiv b)
      (QuadricNormalHomogenization.polynomial L Q)) at hh
    rw [FirstChartCoordinateEquiv.lift_quadric] at hh
    change Irreducible (QuadricNormalHomogenization.polynomial
      (FirstCoordinateShear.substitute b L) Q') at hh
    rw [hb] at hh
    exact hh
  have hboundary := QuadricNormalHomogenization.boundary_nonzero a Q' hQ' hi
  let T := S.image (FirstCoordinateShear.point (-b))
  have hT : ∀ w ∈ T, a * w 0 + eval w Q' = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    have he := hS v hv
    have hback : FirstCoordinateShear.point b (FirstCoordinateShear.point (-b) v) = v := by
      rw [FirstCoordinateShear.point_add, add_neg_cancel]
      simp only [FirstCoordinateShear.point, Pi.zero_apply, zero_mul, sum_const_zero,
        add_zero, Fin.cons_self_tail]
    have hLe := FirstCoordinateShear.evaluation b L (FirstCoordinateShear.point (-b) v)
    rw [hb, hback, map_mul, eval_C, eval_X] at hLe
    have hQe := FirstCoordinateShear.evaluation b Q (FirstCoordinateShear.point (-b) v)
    rw [hback] at hQe
    change a * FirstCoordinateShear.point (-b) v 0 +
      eval (FirstCoordinateShear.point (-b) v) (FirstCoordinateShear.substitute b Q) = 0
    rw [hQe, hLe]
    exact he
  have hc := FiniteFieldQuadricNormalCount.cardinality_bound a ha Q' hQ' hboundary T hT
  rw [card_image_of_injective _ (FirstCoordinateShear.point_injective (-b))] at hc
  exact hc

theorem cardinality_bound (L Q : MvPolynomial (Fin 3) F)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hQ : Q.IsHomogeneous 2)
    (hirr : Irreducible (QuadricNormalHomogenization.polynomial L Q))
    (S : Finset (Fin 3 → F)) (hS : ∀ v ∈ S, eval v L + eval v Q = 0) :
    S.card ≤ Fintype.card F ^ 2 + 2 * Fintype.card F := by
  obtain ⟨k, hk⟩ := LinearFirstCoordinateNormalization.exists_nonzero_coefficient L hL hL0
  let τ := Equiv.swap (0 : Fin 3) k
  let e := renameEquiv F τ
  have ha : (rename τ L).coeff (Finsupp.single 0 1) ≠ 0 := by
    have hh := coeff_rename_mapDomain τ τ.injective L (Finsupp.single k 1)
    have ht : τ k = 0 := Equiv.swap_apply_right _ _
    rw [Finsupp.mapDomain_single, ht] at hh
    rw [hh]
    exact hk
  have hi : Irreducible (QuadricNormalHomogenization.polynomial (rename τ L) (rename τ Q)) := by
    have hh := (MulEquiv.irreducible_iff (FirstChartCoordinateEquiv.liftEquiv e).toMulEquiv).mpr hirr
    change Irreducible (FirstChartCoordinateEquiv.liftEquiv e
      (QuadricNormalHomogenization.polynomial L Q)) at hh
    rw [FirstChartCoordinateEquiv.lift_quadric] at hh
    exact hh
  let f : (Fin 3 → F) → Fin 3 → F := fun v i ↦ v (τ i)
  have hf : Function.Injective f := by
    intro v w he
    funext i
    have hh := congrFun he (τ i)
    simpa only [f, τ, Equiv.swap_apply_self] using hh
  have hroots : ∀ v ∈ S.image f, eval v (rename τ L) + eval v (rename τ Q) = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    rw [CoordinateSwapEvaluation.evaluation, CoordinateSwapEvaluation.evaluation]
    exact hS v hv
  have hc := first_coefficient_bound (rename τ L) (rename τ Q)
    hL.rename_isHomogeneous hQ.rename_isHomogeneous ha hi (S.image f) hroots
  rw [card_image_of_injective _ hf] at hc
  exact hc

end PaperP1.FiniteFieldQuadricLinearCount
