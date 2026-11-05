module

public import PaperP1.Asymptotics.FixedQuadraticOrdinaryMoments
public import PaperP1.Asymptotics.NominalQuadraticFactorialMoments
public import PaperP1.Asymptotics.FixedHigherCumulants
public import PaperP1.Asymptotics.FixedCountMomentBounds

/-! # All assertions of the original fixed-moment theorem, without unproved inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompleteFixedMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FactorialCountMoments
  PaperP1.CountObservables PaperP1.HeterogeneousDirectMaximum PaperP1.TouchardCountMoments

theorem article_6_4 (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      let G := dyadicBlock N
      let μ := actualMean G L
      let α := RegularCumulantTransfer.secondFactorialCumulant G L
      let ν := FiniteChannelHierarchy.nominalMean N L
      |factorialCountMoment G L r - μ ^ r - (r.choose 2 : ℝ) * μ ^ (r - 2) * α| ≤
        (N : ℝ) ^ (-4 / 5 + ε) ∧
      |factorialCountMoment G L r - ν ^ r -
        (r.choose 2 : ℝ) * ν ^ (r - 2) * SecondFactorialCorrection.value N L| ≤
        (N : ℝ) ^ (-4 / 5 + ε) ∧
      |countMoment G L r - (touchard r).eval μ -
        α / 2 * ((touchard r).derivative.derivative).eval μ| ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
      countMoment G L r ≤ B ∧
      (3 ≤ r → |AllFactorialCumulants.factorialCumulant G L r| ≤ (N : ℝ) ^ (-4 / 5 + ε)) := by
  obtain ⟨NF, _hNF, hf⟩ := FixedQuadraticFactorialMoments.uniform_fixed r hr C ε hε
  obtain ⟨NN, _hNN, hn⟩ := NominalQuadraticFactorialMoments.uniform_fixed r hr C ε hε
  obtain ⟨NO, _hNO, ho⟩ := FixedQuadraticOrdinaryMoments.uniform_fixed r C ε hε
  obtain ⟨NK, _hNK, hk⟩ := FixedHigherCumulants.uniform_fixed (max 3 r) (le_max_left _ _) C ε hε
  obtain ⟨B, hB, NB, _hNB, hb⟩ := FixedCountMomentBounds.uniform_ordinary_bound r C
  refine ⟨B, hB, 10 + NF + NN + NO + NK + NB, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  have hp : (N : ℝ) ^ (-1 + ε) ≤ (N : ℝ) ^ (-4 / 5 + ε) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
  refine ⟨(hf N (by omega) L hband _ Subset.rfl).trans hp,
    (hn N (by omega) L hband).trans hp,
    (ho N (by omega) L hband _ Subset.rfl).trans hp,
    hb N (by omega) L hband _ Subset.rfl, ?_⟩
  intro hthree
  have h := hk N (by omega) L hband (dyadicBlock N) Subset.rfl
  rw [max_eq_right hthree] at h
  exact h.trans hp

end PaperP1.CompleteFixedMoments
