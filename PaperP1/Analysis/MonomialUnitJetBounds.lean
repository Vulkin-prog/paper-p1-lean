module

public import PaperP1.Analysis.UnitJetProductBounds
public import PaperP1.Analysis.AffineUnitGraphParametrization
public import PaperP1.Algebra.TotalDegreeMonomialFamily

/-! # Actual monomial derivative bounds on a plane curve with unit jets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MonomialUnitJetBounds

open MvPolynomial Set TotalDegreeMonomials TotalDegreeMonomialFamily AffineUnitGraphParametrization
open scoped ContDiff

theorem basis_evaluation {k : ℕ} (i : Index k) (z : Fin 2 → ℝ) :
    eval z (basis i) = z 0 ^ i.val.1.val * z 1 ^ i.val.2.val := by
  rw [basis, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Fin.prod_univ_two]
  simp [exponent]

theorem basis_derivative_bound (k r : ℕ) (ψ : Fin 2 → ℝ → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) (hjet : UnitJets r ψ)
    (i : Index k) (j : ℕ) (hj : j ≤ r) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |iteratedDeriv j (fun t ↦ eval (fun a ↦ ψ a t) (basis i)) x| ≤ (k : ℝ) ^ j := by
  have heq : (fun t ↦ eval (fun a ↦ ψ a t) (basis i)) =
      (fun t ↦ ψ 0 t ^ i.val.1.val * ψ 1 t ^ i.val.2.val) := by
    funext t
    exact basis_evaluation i _
  rw [heq]
  have hh := UnitJetProductBounds.two_powers_bound (ψ 0) (ψ 1) x r
    ((hψ 0).contDiffAt (isOpen_Ioo.mem_nhds hx)) ((hψ 1).contDiffAt (isOpen_Ioo.mem_nhds hx))
    (fun a ha ↦ hjet 0 a ha x hx) (fun a ha ↦ hjet 1 a ha x hx) i.val.1.val i.val.2.val j hj
  exact hh.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast i.property) j)

theorem basis_uniform_bound (k r : ℕ) (ψ : Fin 2 → ℝ → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) (hjet : UnitJets r ψ)
    (i : Index k) (j : ℕ) (hj : j ≤ r) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |iteratedDeriv j (fun t ↦ eval (fun a ↦ ψ a t) (basis i)) x| ≤ ((k + 1 : ℕ) : ℝ) ^ r := by
  calc
    _ ≤ (k : ℝ) ^ j := basis_derivative_bound k r ψ hψ hjet i j hj x hx
    _ ≤ ((k + 1 : ℕ) : ℝ) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_succ k)) _
    _ ≤ ((k + 1 : ℕ) : ℝ) ^ r := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ k + 1 by omega)) hj

theorem family_uniform_bound (k r : ℕ) (ψ : Fin 2 → ℝ → ℝ)
    (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) (hjet : UnitJets r ψ)
    (i : Fin (Fintype.card (Index k))) (j : ℕ) (hj : j ≤ r) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    |iteratedDeriv j (fun t ↦ eval (fun a ↦ ψ a t) (family k i)) x| ≤ ((k + 1 : ℕ) : ℝ) ^ r :=
  basis_uniform_bound k r ψ hψ hjet (enumeration k i) j hj x hx

end PaperP1.MonomialUnitJetBounds
