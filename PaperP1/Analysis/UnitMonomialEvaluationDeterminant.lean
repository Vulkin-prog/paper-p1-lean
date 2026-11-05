module

public import PaperP1.Analysis.MonomialUnitJetBounds
public import PaperP1.Analysis.RealSmoothEvaluationDeterminant

/-! # Short-interval determinants of actual curve monomials with unit jets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitMonomialEvaluationDeterminant

open MvPolynomial Set TotalDegreeMonomials TotalDegreeMonomialFamily AffineUnitGraphParametrization
open scoped ContDiff

theorem index_card_two_le (k : ℕ) (hk : 1 ≤ k) : 2 ≤ Fintype.card (Index k) := by
  let e : Fin 2 → Index k := fun i ↦
    ⟨(⟨i.val, by have := i.isLt; omega⟩, ⟨0, by omega⟩), by
      change i.val + 0 ≤ k
      have := i.isLt
      omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun v : Index k ↦ v.val.1.val) h
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he

theorem basis_bound (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (e : Fin n → Index k)
    (ψ : Fin 2 → ℝ → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (n - 1) ψ) (c δ : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Ioo (0 : ℝ) 1) (hdist : ∀ j, |x j - c| ≤ δ) :
    |Matrix.det (fun i j : Fin n ↦ eval (fun a ↦ ψ a (x j)) (basis (e i)))| ≤
      (((2 * n : ℕ) : ℝ)) ^ n * ((k + 1 : ℕ) : ℝ) ^ ((n - 1) * n) *
        (n.factorial : ℝ) * δ ^ (n * (n - 1) / 2) := by
  have hh := RealSmoothEvaluationDeterminant.coarse_bound n hn
    (fun i t ↦ eval (fun a ↦ ψ a t) (basis (e i))) 0 1 c hc
    (fun i ↦ PolynomialEvaluationDerivative.contDiffOn_eval (basis (e i)) ∞ _ ψ hψ)
    (((k + 1 : ℕ) : ℝ) ^ (n - 1)) δ
    (one_le_pow₀ (show (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ k + 1 by omega)))
    hδ hδone x hx hdist
    (fun i j hj y hy ↦ MonomialUnitJetBounds.basis_uniform_bound k (n - 1) ψ hψ hjet (e i) j hj y hy)
  simpa only [← pow_mul] using hh

theorem family_bound (k : ℕ) (hk : 1 ≤ k) (ψ : Fin 2 → ℝ → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (Fintype.card (Index k) - 1) ψ) (c δ : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (x : Fin (Fintype.card (Index k)) → ℝ)
    (hx : ∀ j, x j ∈ Ioo (0 : ℝ) 1) (hdist : ∀ j, |x j - c| ≤ δ) :
    let n := Fintype.card (Index k)
    |Matrix.det (fun i j : Fin n ↦ eval (fun a ↦ ψ a (x j)) (family k i))| ≤
      (((2 * n : ℕ) : ℝ)) ^ n * ((k + 1 : ℕ) : ℝ) ^ ((n - 1) * n) *
        (n.factorial : ℝ) * δ ^ (n * (n - 1) / 2) :=
  basis_bound _ (index_card_two_le k hk) k (enumeration k) ψ hψ hjet c δ hc hδ hδone x hx hdist

end PaperP1.UnitMonomialEvaluationDeterminant
