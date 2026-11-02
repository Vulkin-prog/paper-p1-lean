module

public import PaperP1.Combinatorics.TouchingEdgeWeights
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.IrregularSeedMass

/-! # All actual covariance edges touching an irregular site cost N^(-1+epsilon)

The proof is unconditional and retains the exact original marginals,
including those equal to zero.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IrregularPairActivity

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RegularStarts

def pairs (N L : ℕ) (G : Finset ℕ) : Finset (Finset ℕ) :=
  TouchingEdgeWeights.touching G (G ∩ irregularStarts N L)

theorem finite_bound (N L : ℕ) (G : Finset ℕ) :
    CompatibleActivitySplit.absolute L (pairs N L G) ≤
      ∑ x ∈ G ∩ irregularStarts N L, PairRowActivity.absoluteRow G L x :=
  TouchingEdgeWeights.sum_bound G (G ∩ irregularStarts N L) inter_subset_left
    (fun e ↦ |infiniteCenteredCoefficient L e|) (fun _ ↦ abs_nonneg _)

theorem uniform_marginal_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ x ∈ irregularStarts N L, infiniteMarginal x L) ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NI, hi⟩ := IrregularSeedMass.affine_sum C δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * (2 : ℝ) ^ C) (-1 + δ) δ hδ
  refine ⟨max 2 (max NI (max NG NF)), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hmass : (∑ x ∈ irregularStarts N L, infiniteMarginal x L) ≤
      (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + δ) := by
    simpa only [RegularAffineBounds.affineWindowMass, infiniteMarginal_eq_affine_atom hL] using
      hi N (by omega) L hL hband (fun _ ↦ startRhs L)
  calc
    _ ≤ _ := hmass
    _ ≤ (N : ℝ) ^ ((-1 + δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

theorem uniform_activity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (pairs N L G) ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NM, _hNM, hm⟩ := uniform_marginal_mass C δ hδ
  obtain ⟨NR, _hNR, hr⟩ := ActualPairRowActivity.uniform_absolute_row C δ hδ
  refine ⟨max 2 (max NM NR), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ ∑ x ∈ G ∩ irregularStarts N L, PairRowActivity.absoluteRow G L x := finite_bound N L G
    _ ≤ ∑ x ∈ G ∩ irregularStarts N L, (N : ℝ) ^ δ * infiniteMarginal x L := by
      apply sum_le_sum
      intro x hx
      exact hr N (by omega) L hband G hG x (hG (mem_inter.mp hx).1)
    _ = (N : ℝ) ^ δ * ∑ x ∈ G ∩ irregularStarts N L, infiniteMarginal x L := (mul_sum _ _ _).symm
    _ ≤ (N : ℝ) ^ δ * ∑ x ∈ irregularStarts N L, infiniteMarginal x L :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg inter_subset_right
        (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)) (by positivity)
    _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (-1 + δ) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband) (by positivity)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [δ]; ring

end PaperP1.IrregularPairActivity
