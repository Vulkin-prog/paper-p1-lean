module

public import PaperP1.Analysis.MonomialWronskianExceptions
public import PaperP1.Analysis.TangentCurvePieceZeros

/-! # Every bounded-degree polynomial on a nonexceptional actual curve piece

The concrete monomial reconstruction supplies all polynomial combinations.
Distinct point populations are counted without an injective parametrization.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonomialCurvePieceCount

open MvPolynomial Finset Set TotalDegreeMonomials TotalDegreeMonomialFamily
  MonomialWronskianExceptions NonstationaryTangentImage CurvePolynomialWronskianNonvanishing

theorem partial_nonzero (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (r : RegularPiece P)
    (hnon : ∀ t ∈ Ioo r.left r.right, position r.path t ∉ exceptionalPoints P k) :
    TangentCurvePieceZeros.PartialPolynomialNonzero P (family k) r.path (Ioo r.left r.right) := by
  intro j hj hjpos t ht hzero
  cases j with
  | zero => omega
  | succ j =>
    apply hnon t ht
    exact ⟨r.equation t ht, ⟨⟨j, by omega⟩, hzero⟩⟩

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (r : RegularPiece P)
    (hnon : ∀ t ∈ Ioo r.left r.right, position r.path t ∉ exceptionalPoints P k)
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) (hdegree : Q.totalDegree ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo r.left r.right, position r.path t = z) ∧ eval z Q = 0) :
    S.card < Fintype.card (Index k) := by
  apply TangentCurvePieceZeros.image_zero_bound P _ (family k) r.path r.left r.right
    r.trajectory (partial_nonzero P k r hnon) (coordinates k Q) (coordinates_ne_zero k Q hdegree hQ) S
  intro z hz
  refine ⟨(hS z hz).1, ?_⟩
  rw [← combination_evaluation, reconstruction k Q hdegree]
  exact (hS z hz).2

end PaperP1.MonomialCurvePieceCount
