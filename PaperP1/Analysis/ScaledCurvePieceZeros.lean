module

public import PaperP1.Analysis.ScaledPolynomialTangentTrajectory
public import PaperP1.Analysis.TangentCurvePieceZeros

/-! # Actual zero counts on smoothly and nontrivially scaled curve pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledCurvePieceZeros

open MvPolynomial Finset Set ScaledPolynomialTangentTrajectory
open scoped ContDiff

theorem partial_evaluation (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ) {n : ℕ}
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ)
    (hs : IsOpen s) (ha : ContDiffOn ℝ ∞ a s) (hscale : ∀ t ∈ s, a t ≠ 0)
    (hφ : Trajectory P a φ s) (hW : TangentCurvePieceZeros.PartialPolynomialNonzero P f φ s) :
    PolyaChebyshevCriterion.PartialNonzero (fun i u ↦ eval (fun k ↦ φ k u) (f i)) s := by
  intro j hj hjpos t ht
  exact wronskian_ne_zero P a φ s hs ha hφ j (fun i ↦ f (Fin.castLE hj i)) t ht
    (hscale t ht) (hW j hj hjpos t ht)

theorem parameter_zero_bound (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ) (n : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (l v : ℝ)
    (ha : ContDiffOn ℝ ∞ a (Ioo l v)) (hscale : ∀ t ∈ Ioo l v, a t ≠ 0)
    (hφ : Trajectory P a φ (Ioo l v))
    (hW : TangentCurvePieceZeros.PartialPolynomialNonzero P f φ (Ioo l v))
    (c : Fin n → ℝ) (hc : c ≠ 0) (T : Finset ℝ)
    (hT : ∀ t ∈ T, t ∈ Ioo l v ∧ ∑ i, c i * eval (fun k ↦ φ k t) (f i) = 0) :
    T.card < n := by
  have hsmooth := contDiffOn_trajectory P a φ (Ioo l v) isOpen_Ioo ha hφ
  exact PolyaChebyshevCriterion.card_lt n l v (fun i u ↦ eval (fun k ↦ φ k u) (f i))
    (fun i ↦ PolynomialEvaluationDerivative.contDiffOn_eval (f i) ∞ (Ioo l v) φ hsmooth)
    (partial_evaluation P a f φ (Ioo l v) isOpen_Ioo ha hscale hφ hW) c hc T hT

theorem image_zero_bound (P : MvPolynomial (Fin 2) ℝ) (a : ℝ → ℝ) (n : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (l v : ℝ)
    (ha : ContDiffOn ℝ ∞ a (Ioo l v)) (hscale : ∀ t ∈ Ioo l v, a t ≠ 0)
    (hφ : Trajectory P a φ (Ioo l v))
    (hW : TangentCurvePieceZeros.PartialPolynomialNonzero P f φ (Ioo l v))
    (c : Fin n → ℝ) (hc : c ≠ 0) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo l v, (fun k ↦ φ k t) = z) ∧ ∑ i, c i * eval z (f i) = 0) :
    S.card < n := by
  classical
  have hex (z : S) : ∃ t ∈ Ioo l v, (fun k ↦ φ k t) = z.val := (hS z.val z.property).1
  choose τ hτ hpoint using hex
  have hinj : Function.Injective τ := by
    intro z w heq
    apply Subtype.ext
    rw [← hpoint z, ← hpoint w, heq]
  let T : Finset ℝ := Finset.univ.image τ
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  have hT : ∀ t ∈ T, t ∈ Ioo l v ∧ ∑ i, c i * eval (fun k ↦ φ k t) (f i) = 0 := by
    intro t ht
    obtain ⟨z, _hz, rfl⟩ := mem_image.mp ht
    refine ⟨hτ z, ?_⟩
    rw [hpoint z]
    exact (hS z.val z.property).2
  have hh := parameter_zero_bound P a n f φ l v ha hscale hφ hW c hc T hT
  rw [hcard] at hh
  exact hh

end PaperP1.ScaledCurvePieceZeros
