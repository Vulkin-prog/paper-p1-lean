module

public import PaperP1.Diophantine.FiniteFieldQuadricFirstChartCount
public import PaperP1.Algebra.P3FieldChartExchange

/-! # The original X3=1 quadric chart with every original point retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteFieldQuadricLastChartCount

open MvPolynomial Finset
open scoped Classical

theorem cardinality_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 2) (hirr : Irreducible P)
    (a : Fin 3 → F) (ha : eval (Fin.snoc a 1) P = 0)
    (hgrad : ∃ k : Fin 4, eval (Fin.snoc a 1) (pderiv k P) ≠ 0)
    (S : Finset (Fin 3 → F)) (hS : ∀ v ∈ S, eval (Fin.snoc v 1) P = 0) :
    S.card ≤ Fintype.card F ^ 2 + 2 * Fintype.card F := by
  let P' := rename P3FieldChartExchange.permutation P
  have hP' : P'.IsHomogeneous 2 := hP.rename_isHomogeneous
  have hi : Irreducible P' :=
    (MulEquiv.irreducible_iff (renameEquiv F P3FieldChartExchange.permutation).toMulEquiv).mpr hirr
  have ha' : eval (Fin.cons 1 (P3FieldChartExchange.point a)) P' = 0 := by
    rw [P3FieldChartExchange.evaluation]
    exact ha
  have hgrad' : ∃ k : Fin 4,
      eval (Fin.cons 1 (P3FieldChartExchange.point a)) (pderiv k P') ≠ 0 := by
    obtain ⟨k, hk⟩ := hgrad
    refine ⟨P3FieldChartExchange.permutation k, ?_⟩
    rw [P3FieldChartExchange.evaluation_partial]
    exact hk
  have hfree := P3FieldChartExchange.free_gradient P' hP' (P3FieldChartExchange.point a) ha' hgrad'
  let T := S.image P3FieldChartExchange.point
  have hT : ∀ w ∈ T, eval (Fin.cons 1 w) P' = 0 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    rw [P3FieldChartExchange.evaluation]
    exact hS v hv
  have hc := FiniteFieldQuadricFirstChartCount.cardinality_bound P' hP' hi
    (P3FieldChartExchange.point a) ha' hfree T hT
  rw [card_image_of_injective _ P3FieldChartExchange.point_injective] at hc
  exact hc

end PaperP1.FiniteFieldQuadricLastChartCount
