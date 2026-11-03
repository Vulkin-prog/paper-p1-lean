module

public import PaperP1.Asymptotics.ExceptionalPolynomialMomentsUnderInputs
public import PaperP1.Asymptotics.RetainedGoodPairScale
public import PaperP1.Asymptotics.PoissonCharlierConversion
public import PaperP1.Model.RetainedPairMomentGenerator

/-! # Fixed pair leakage is smaller than the pair scale, while its full weighted generator is bounded without geometry -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedPairLeakageUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CountObservables
  PaperP1.RetainedActiveSubsetMoments PaperP1.RetainedPairMomentGenerator PaperP1.RegularStarts
  PaperP1.RetainedExceptionalEventUnderInputs

theorem pair_leakage_eq (H : ℝ) (N L r : ℕ) : pairLeakage H N L r =
    ActiveSetExceptionalMoment.value H N L (regularStarts N L) (fun A ↦ (pair H N L r A : ℝ)) := rfl

theorem uniform_fixed_pair (C : ℝ) :
    ∃ p : Parameters, Hypotheses p (1 / 120) → ∀ r : ℕ,
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        pairLeakage (8 * (L + 1) : ℕ) N L r ≤ (N : ℝ) ^ (-83 / 120 : ℝ) := by
  obtain ⟨p, hp⟩ := ExceptionalPolynomialMomentsUnderInputs.uniform_fixed C
  refine ⟨p, ?_⟩
  intro hgeo r
  obtain ⟨N₀, hN₀, h⟩ := hp hgeo (r + 2)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband
  rw [pair_leakage_eq]
  apply h N hN L hband (regularStarts N L) (regularStarts_subset N L)
  intro A _hAG
  refine ⟨Nat.cast_nonneg _, ?_⟩
  exact_mod_cast RetainedSubsetCounts.pairCount_le_power (fun x ↦ squareClassSpace x L)
    (GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L)
    (RetainedGoodEdges.good_pair_card (8 * (L + 1) : ℕ) N L) A r

theorem uniform_generator_bound (C : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ,
      leakageSum 4 H N L ≤ A * SecondFactorialCorrection.value N L := by
  obtain ⟨K, hK, NK, _hNK, hk⟩ := RetainedGoodPairScale.uniform_bound C
  obtain ⟨NC, _hNC, hc⟩ := PoissonCharlierConversion.regular_card_eventually C
  obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let M : ℝ := 2 * (2 : ℝ) ^ C
  let E := Real.exp (4 * M)
  refine ⟨16 * K * E, by dsimp only [E]; positivity, 10 + NK + NC + NM + NG, by omega, ?_⟩
  intro N hN L hband H
  have hN2 : 2 ≤ N := by omega
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hmean : countMoment (regularStarts N L) L 1 ≤ M :=
    (RegularMomentTransfer.countMoment_mono (Subset.refl (dyadicBlock N)) (regularStarts_subset N L) 1).trans
      (hm N (by omega) L hband).2
  have hexp : Real.exp (4 * countMoment (regularStarts N L) L 1) ≤ E :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmean (by norm_num))
  have hβ := hk N (by omega) L hband H
  have hprod := mul_le_mul hβ hexp (Real.exp_nonneg _ ) ((beta_nonneg H N L).trans hβ)
  calc
    _ ≤ meanSum 4 H N L := leakage_le_mean 4 H N L (by norm_num)
    _ ≤ (4 : ℝ) ^ 2 * RetainedReferenceTheorem.beta H N L * Real.exp (4 * countMoment (regularStarts N L) L 1) :=
      exponential_bound hN2 hL H 4 (by norm_num) (hc N (by omega) L hband)
    _ = 16 * (RetainedReferenceTheorem.beta H N L * Real.exp (4 * countMoment (regularStarts N L) L 1)) := by ring
    _ ≤ 16 * ((K * SecondFactorialCorrection.value N L) * E) := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := by ring

end PaperP1.RetainedPairLeakageUnderInputs
