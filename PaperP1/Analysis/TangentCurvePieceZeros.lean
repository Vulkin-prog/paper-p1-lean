module

public import PaperP1.Analysis.PolynomialTangentTrajectory
public import PaperP1.Analysis.PolyaChebyshevCriterion

/-! # Actual finite point populations on a nonexceptional tangent curve piece

Polynomial partial-Wronskian nonvanishing is converted into a strict zero count.
The final point estimate needs no injectivity assumption on the trajectory.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TangentCurvePieceZeros

open MvPolynomial Finset Set PolynomialTangentTrajectory
open scoped ContDiff

def PartialPolynomialNonzero (P : MvPolynomial (Fin 2) ℝ) {n : ℕ}
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ j : ℕ, ∀ hj : j ≤ n, 0 < j → ∀ t ∈ s,
    eval (fun k ↦ φ k t) (PolynomialTangentWronskian.wronskian P j
      (fun i ↦ f (Fin.castLE hj i))) ≠ 0

theorem partial_evaluation (P : MvPolynomial (Fin 2) ℝ) {n : ℕ}
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ)
    (s : Set ℝ) (hs : IsOpen s) (hφ : Trajectory P φ s)
    (hW : PartialPolynomialNonzero P f φ s) :
    PolyaChebyshevCriterion.PartialNonzero (fun i u ↦ eval (fun k ↦ φ k u) (f i)) s := by
  intro j hj hjpos t ht
  have hh := hW j hj hjpos t ht
  rw [← wronskian_evaluation P φ s hs hφ j (fun i ↦ f (Fin.castLE hj i)) t ht] at hh
  exact hh

theorem parameter_zero_bound (P : MvPolynomial (Fin 2) ℝ) (n : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (a b : ℝ)
    (hφ : Trajectory P φ (Ioo a b)) (hW : PartialPolynomialNonzero P f φ (Ioo a b))
    (c : Fin n → ℝ) (hc : c ≠ 0) (T : Finset ℝ)
    (hT : ∀ t ∈ T, t ∈ Ioo a b ∧ ∑ i, c i * eval (fun k ↦ φ k t) (f i) = 0) :
    T.card < n := by
  have hsmooth := contDiffOn_trajectory P φ (Ioo a b) isOpen_Ioo hφ
  exact PolyaChebyshevCriterion.card_lt n a b (fun i u ↦ eval (fun k ↦ φ k u) (f i))
    (fun i ↦ PolynomialEvaluationDerivative.contDiffOn_eval (f i) ∞ (Ioo a b) φ hsmooth)
    (partial_evaluation P f φ (Ioo a b) isOpen_Ioo hφ hW) c hc T hT

theorem image_zero_bound (P : MvPolynomial (Fin 2) ℝ) (n : ℕ)
    (f : Fin n → MvPolynomial (Fin 2) ℝ) (φ : Fin 2 → ℝ → ℝ) (a b : ℝ)
    (hφ : Trajectory P φ (Ioo a b)) (hW : PartialPolynomialNonzero P f φ (Ioo a b))
    (c : Fin n → ℝ) (hc : c ≠ 0) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ z ∈ S, (∃ t ∈ Ioo a b, (fun k ↦ φ k t) = z) ∧ ∑ i, c i * eval z (f i) = 0) :
    S.card < n := by
  classical
  have hex (z : S) : ∃ t ∈ Ioo a b, (fun k ↦ φ k t) = z.val := (hS z.val z.property).1
  choose τ hτ hpoint using hex
  have hinj : Function.Injective τ := by
    intro z w heq
    apply Subtype.ext
    rw [← hpoint z, ← hpoint w, heq]
  let T : Finset ℝ := Finset.univ.image τ
  have hcard : T.card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, card_univ, Fintype.card_coe]
  have hT : ∀ t ∈ T, t ∈ Ioo a b ∧ ∑ i, c i * eval (fun k ↦ φ k t) (f i) = 0 := by
    intro t ht
    obtain ⟨z, _hz, rfl⟩ := mem_image.mp ht
    refine ⟨hτ z, ?_⟩
    rw [hpoint z]
    exact (hS z.val z.property).2
  have hh := parameter_zero_bound P n f φ a b hφ hW c hc T hT
  rw [hcard] at hh
  exact hh

end PaperP1.TangentCurvePieceZeros
