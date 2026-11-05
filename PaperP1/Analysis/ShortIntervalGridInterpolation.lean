module

public import PaperP1.Analysis.GridCurveMinorVanishing
public import PaperP1.Algebra.FiniteEvaluationAnnihilator

/-! # Constructed auxiliary polynomials on actual short-interval grid populations

Every maximal minor is proved zero before selecting a common nonzero
coefficient vector. The population index type need not itself be finite.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortIntervalGridInterpolation

open MvPolynomial Set Finset TotalDegreeMonomials TotalDegreeMonomialFamily
  AffineUnitGraphParametrization CurvePolynomialWronskianNonvanishing GridCurveMinorVanishing
open scoped ContDiff

theorem exists_polynomial {ι : Type*} (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 0 < N)
    (ψ : Fin 2 → ℝ → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (Fintype.card (Index k) - 1) ψ) (c δ : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (x : ι → ℝ)
    (hx : ∀ j, x j ∈ Ioo (0 : ℝ) 1) (hdist : ∀ j, |x j - c| ≤ δ)
    (z : ι → Fin 2 → ℤ) (hgrid : ∀ j a, ψ a (x j) = (z j a : ℝ) / N)
    (hsmall : (N : ℝ) ^ (k * Fintype.card (Index k)) * analyticBudget (Fintype.card (Index k)) k δ < 1) :
    ∃ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 ∧ Q.totalDegree ≤ k ∧
      ∀ j, eval (fun a ↦ ψ a (x j)) Q = 0 := by
  classical
  let n := Fintype.card (Index k)
  let rows : ι → Fin n → ℝ := fun j i ↦ eval (fun a ↦ ψ a (x j)) (family k i)
  have hdet : ∀ f : Fin n → ι, Function.Injective f → Matrix.det (fun i j ↦ rows (f i) j) = 0 := by
    intro f _hf
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ rows (f i) j
    have hv : A.transpose.det = 0 := by
      change Matrix.det (fun i j : Fin n ↦ eval (fun a ↦ ψ a (x (f j))) (basis (enumeration k i))) = 0
      exact vanishing n (UnitMonomialEvaluationDeterminant.index_card_two_le k hk) k (enumeration k) N hN
        ψ hψ hjet c δ hc hδ hδone (fun j ↦ x (f j)) (fun j ↦ hx (f j)) (fun j ↦ hdist (f j))
        (fun j ↦ z (f j)) (fun j a ↦ hgrid (f j) a) hsmall
    exact (Matrix.det_transpose A).symm.trans hv
  obtain ⟨w, hw, hzero⟩ := FiniteEvaluationAnnihilator.coefficients rows hdet
  refine ⟨polynomialCombination (family k) w,
    combination_ne_zero k n (enumeration k) (enumeration k).injective w hw,
    combination_degree (family k) k (fun i ↦ basis_degree (enumeration k i)) w, ?_⟩
  intro j
  rw [combination_evaluation]
  calc
    _ = ∑ i, rows j i * w i := by
      apply sum_congr rfl
      intro i _hi
      exact mul_comm _ _
    _ = 0 := hzero j

end PaperP1.ShortIntervalGridInterpolation
