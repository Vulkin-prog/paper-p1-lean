module

public import PaperP1.Algebra.HomogeneousQuadricFirstChart
public import PaperP1.Diophantine.FiniteFieldQuadricLinearCount

/-! # Every original first-chart point of an irreducible quadric with one smooth point is counted -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldQuadricFirstChartCount

open MvPolynomial Finset
open scoped Classical

theorem cardinality_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2) (hirr : Irreducible P)
    (a : Fin 3 → F) (ha : eval (Fin.cons 1 a) P = 0)
    (hgrad : ∃ i : Fin 3, eval (Fin.cons 1 a) (pderiv i.succ P) ≠ 0)
    (S : Finset (Fin 3 → F)) (hS : ∀ v ∈ S, eval (Fin.cons 1 v) P = 0) :
    S.card ≤ Fintype.card F ^ 2 + 2 * Fintype.card F := by
  let P' := HomogeneousLinearShear.substitute a P
  have hP' : P'.IsHomogeneous 2 := HomogeneousLinearShear.homogeneous a P hP
  have hi : Irreducible P' := by
    exact (MulEquiv.irreducible_iff (HomogeneousLinearShear.equiv a).toMulEquiv).mpr hirr
  have hroot : eval (Fin.cons 1 0) P' = 0 := by
    rw [HomogeneousLinearShear.eval_substitute]
    exact ha
  have hgrad' : ∃ i : Fin 3, eval (Fin.cons 1 0) (pderiv i.succ P') ≠ 0 := by
    obtain ⟨i, hi⟩ := hgrad
    refine ⟨i, ?_⟩
    rw [HomogeneousFirstChartTranslation.origin_free_partial]
    exact hi
  let L := (finSuccEquiv F 3 P').coeff 1
  let Q := (finSuccEquiv F 3 P').coeff 0
  have hL : L.IsHomogeneous 1 := hP'.finSuccEquiv_coeff_isHomogeneous 1 1 rfl
  have hQ : Q.IsHomogeneous 2 := hP'.finSuccEquiv_coeff_isHomogeneous 0 2 rfl
  have hL0 : L ≠ 0 := HomogeneousQuadricFirstChart.linear_part_nonzero P' hP' hroot hgrad'
  have heq : P' = QuadricNormalHomogenization.polynomial L Q :=
    HomogeneousQuadricFirstChart.decomposition P' hP' hroot
  have hirr' : Irreducible (QuadricNormalHomogenization.polynomial L Q) := heq ▸ hi
  let f : (Fin 3 → F) → Fin 3 → F := fun v ↦ v - a
  have hf : Function.Injective f := by
    intro v w h
    have hh := congrArg (fun u : Fin 3 → F ↦ u + a) h
    simpa only [f, sub_add_cancel] using hh
  have hroots : ∀ w ∈ S.image f, eval w L + eval w Q = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    rw [← QuadricNormalHomogenization.evaluation, ← heq]
    change eval (Fin.cons 1 (v - a)) (HomogeneousLinearShear.substitute a P) = 0
    rw [HomogeneousFirstChartTranslation.evaluation, sub_add_cancel]
    exact hS v hv
  have hc := FiniteFieldQuadricLinearCount.cardinality_bound L Q hL hL0 hQ hirr' (S.image f) hroots
  rw [card_image_of_injective _ hf] at hc
  exact hc

end PaperP1.FiniteFieldQuadricFirstChartCount
