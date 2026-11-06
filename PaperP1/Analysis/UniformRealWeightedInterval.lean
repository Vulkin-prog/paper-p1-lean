module

public import PaperP1.Analysis.DyadicPartialSummation
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.CommonPresenceWeightedSum
public import PaperP1.Analysis.UniformPresenceWeightedSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformRealWeightedInterval
open Finset Filter PaperP1 LogarithmicPhase
open scoped Classical

theorem value_eq_weighted_sum (N M : ℕ) (P Q : Finset ℕ) (f : ℕ →* ℝ) (τ : ℝ) :
    DirichletPolynomialMeanValue.value (Ico N M) (NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ))) τ=
      ∑ n ∈ Ico N M, (NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ)) n*
        phase (-Real.log (n : ℝ)) τ)/(n : ℂ) := by
  unfold DirichletPolynomialMeanValue.value GaussianExponentialSums.polynomial
  apply sum_congr rfl
  intro n hn
  ring

theorem uniform_bound (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (N : ℝ)^B → ∀ M : ℕ, N ≤ M → M ≤ 2*N →
      ‖DirichletPolynomialMeanValue.value (Ico N M)
        (NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ))) τ‖ ≤ ε := by
  obtain ⟨R,hR,T₀,hT₀,X₀,hX₀,hBound⟩ := UniformPresenceWeightedSum.uniform_bound (2*B) (ε/4) (by positivity) (by positivity)
  refine ⟨R,hR,T₀,hT₀,max 4 (2*X₀+2),by omega,?_⟩
  intro N hN P hP Q hQ f hf τ hLower hUpper M hNM hM2
  let a := fun n : ℕ ↦ NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ)) n*phase (-Real.log (n : ℝ)) τ
  have hPartial : ∀ J : ℕ, N-1 ≤ J → J ≤ 2*N → ‖∑ n ∈ Icc 1 J, a n‖ ≤ (ε/4)*(J : ℝ) := by
    intro J hNJ hJ2
    have hJCut : X₀ ≤ J := by omega
    have hJTwo : 2 ≤ J := by omega
    have hN2J : N ≤ 2*J := by omega
    have hJSquare : 2*J ≤ J^2 := by
      simpa only [pow_two] using Nat.mul_le_mul_right J hJTwo
    have hNum : (N : ℝ) ≤ (J : ℝ)^2 := by exact_mod_cast hN2J.trans hJSquare
    have hPower : (N : ℝ)^B ≤ (J : ℝ)^(2*B) := by
      have hh := Real.rpow_le_rpow (Nat.cast_nonneg N) hNum hB.le
      simpa only [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg J),Nat.cast_ofNat] using hh
    change ‖CommonPresenceWeightedSum.weighted J P Q f τ‖ ≤ (ε/4)*(J : ℝ)
    exact hBound J hJCut P hP Q hQ f hf τ hLower (hUpper.trans hPower)
  have hh := DyadicPartialSummation.weighted_interval_bound N M (by omega) hNM hM2 a (ε/4) (by positivity) hPartial
  rw [value_eq_weighted_sum]
  exact hh.trans_eq (by ring)
end PaperP1.UniformRealWeightedInterval
