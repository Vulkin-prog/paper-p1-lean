module

public import PaperP1.Diophantine.CommonGridMonomialDeterminant
public import PaperP1.Analysis.UnitMonomialEvaluationDeterminant

/-! # Actual small-interval grid-curve minors vanish

The real Taylor bound is compared with the proved integer separation after
clearing the actual common grid denominator.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GridCurveMinorVanishing

open MvPolynomial Set TotalDegreeMonomials TotalDegreeMonomialFamily AffineUnitGraphParametrization
open scoped ContDiff

def analyticBudget (n k : ℕ) (δ : ℝ) : ℝ :=
  (((2 * n : ℕ) : ℝ)) ^ n * ((k + 1 : ℕ) : ℝ) ^ ((n - 1) * n) *
    (n.factorial : ℝ) * δ ^ (n * (n - 1) / 2)

theorem vanishing (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (e : Fin n → Index k) (N : ℕ) (hN : 0 < N)
    (ψ : Fin 2 → ℝ → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (n - 1) ψ) (c δ : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (x : Fin n → ℝ)
    (hx : ∀ j, x j ∈ Ioo (0 : ℝ) 1) (hdist : ∀ j, |x j - c| ≤ δ)
    (z : Fin n → Fin 2 → ℤ) (hgrid : ∀ j a, ψ a (x j) = (z j a : ℝ) / N)
    (hsmall : (N : ℝ) ^ (k * n) * analyticBudget n k δ < 1) :
    Matrix.det (fun i j : Fin n ↦ eval (fun a ↦ ψ a (x j)) (basis (e i))) = 0 := by
  have hbound := UnitMonomialEvaluationDeterminant.basis_bound n hn k e ψ hψ hjet c δ hc hδ hδone x hx hdist
  have he : CommonGridMonomialDeterminant.normalizedMatrix e N z =
      (fun i j : Fin n ↦ eval (fun a ↦ ψ a (x j)) (basis (e i))) := by
    ext i j
    change eval (fun a ↦ (z j a : ℝ) / N) (basis (e i)) = _
    have hz : (fun a ↦ (z j a : ℝ) / N) = (fun a ↦ ψ a (x j)) :=
      funext (fun a ↦ (hgrid j a).symm)
    rw [hz]
  rw [← he] at hbound ⊢
  apply CommonGridMonomialDeterminant.zero_of_small n k N hN e z
  have hweight : (N : ℝ) ^ CommonGridMonomialDeterminant.weight e ≤ (N : ℝ) ^ (k * n) :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ N by omega))
      (CommonGridMonomialDeterminant.weight_bound n k e)
  exact (mul_le_mul hweight hbound (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)).trans_lt hsmall

end PaperP1.GridCurveMinorVanishing
