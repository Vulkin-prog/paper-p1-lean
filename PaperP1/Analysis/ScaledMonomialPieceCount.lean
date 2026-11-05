module

public import PaperP1.Analysis.ScaledCurvePieceZeros
public import PaperP1.Analysis.NormalizedScaledTangent
public import PaperP1.Analysis.MonomialWronskianExceptions

/-! # Every bounded-degree polynomial on actual scaled and normalized graph pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledMonomialPieceCount

open MvPolynomial Finset Set TotalDegreeMonomials TotalDegreeMonomialFamily
  MonomialWronskianExceptions CurvePolynomialWronskianNonvanishing
open scoped ContDiff

theorem partial_nonzero (P : MvPolynomial (Fin 2) ℝ) (k : ℕ)
    (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) (hcurve : ∀ t ∈ s, eval (fun i ↦ φ i t) P = 0)
    (hnon : ∀ t ∈ s, (fun i ↦ φ i t) ∉ exceptionalPoints P k) :
    TangentCurvePieceZeros.PartialPolynomialNonzero P (family k) φ s := by
  intro j hj hjpos t ht hzero
  cases j with
  | zero => omega
  | succ j =>
    apply hnon t ht
    exact ⟨hcurve t ht, ⟨⟨j, by omega⟩, hzero⟩⟩

theorem point_count (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (a : ℝ → ℝ)
    (φ : Fin 2 → ℝ → ℝ) (l v : ℝ) (ha : ContDiffOn ℝ ∞ a (Ioo l v))
    (hscale : ∀ t ∈ Ioo l v, a t ≠ 0)
    (hφ : ScaledPolynomialTangentTrajectory.Trajectory P a φ (Ioo l v))
    (hcurve : ∀ t ∈ Ioo l v, eval (fun i ↦ φ i t) P = 0)
    (hnon : ∀ t ∈ Ioo l v, (fun i ↦ φ i t) ∉ exceptionalPoints P k)
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) (hdegree : Q.totalDegree ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo l v, (fun i ↦ φ i t) = z) ∧ eval z Q = 0) :
    S.card < Fintype.card (Index k) := by
  apply ScaledCurvePieceZeros.image_zero_bound P a _ (family k) φ l v ha hscale hφ
    (partial_nonzero P k φ _ hcurve hnon) (coordinates k Q) (coordinates_ne_zero k Q hdegree hQ) S
  intro z hz
  refine ⟨(hS z hz).1, ?_⟩
  rw [← combination_evaluation, reconstruction k Q hdegree]
  exact (hS z hz).2

theorem first_point_count (P : MvPolynomial (Fin 2) ℝ) (k : ℕ)
    (φ : Fin 2 → ℝ → ℝ) (l v : ℝ) (hφ : GraphTangentEvaluation.Trajectory P φ (Ioo l v))
    (hcurve : ∀ t ∈ Ioo l v, eval (fun i ↦ φ i t) P = 0)
    (hnon : ∀ t ∈ Ioo l v, (fun i ↦ φ i t) ∉ exceptionalPoints P k)
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) (hdegree : Q.totalDegree ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo l v, (fun i ↦ φ i t) = z) ∧ eval z Q = 0) :
    S.card < Fintype.card (Index k) :=
  point_count P k (NormalizedScaledTangent.firstScale P φ) φ l v
    (NormalizedScaledTangent.firstScale_smooth P φ _ isOpen_Ioo hφ)
    (NormalizedScaledTangent.firstScale_ne_zero P φ _ hφ)
    (NormalizedScaledTangent.first_trajectory P φ _ hφ) hcurve hnon Q hQ hdegree S hS

theorem second_point_count (P : MvPolynomial (Fin 2) ℝ) (k : ℕ)
    (φ : Fin 2 → ℝ → ℝ) (l v : ℝ) (hφ : TransposedNormalizedGraphPiece.Trajectory P φ (Ioo l v))
    (hcurve : ∀ t ∈ Ioo l v, eval (fun i ↦ φ i t) P = 0)
    (hnon : ∀ t ∈ Ioo l v, (fun i ↦ φ i t) ∉ exceptionalPoints P k)
    (Q : MvPolynomial (Fin 2) ℝ) (hQ : Q ≠ 0) (hdegree : Q.totalDegree ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo l v, (fun i ↦ φ i t) = z) ∧ eval z Q = 0) :
    S.card < Fintype.card (Index k) :=
  point_count P k (NormalizedScaledTangent.secondScale P φ) φ l v
    (NormalizedScaledTangent.secondScale_smooth P φ _ isOpen_Ioo hφ)
    (NormalizedScaledTangent.secondScale_ne_zero P φ _ hφ)
    (NormalizedScaledTangent.second_trajectory P φ _ hφ) hcurve hnon Q hQ hdegree S hS

end PaperP1.ScaledMonomialPieceCount
