module

public import PaperP1.Model.ThirdRunActivityComparison
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import Mathlib.Tactic.FieldSimp

/-! # Uniform repeated-index control using the actual critical-band marginals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RepeatedRunCost

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem mean_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N)
    (hN : 0 < N) (K : ℝ) (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ K / N) (hK : 0 ≤ K) :
    (∑ x ∈ G, infiniteMarginal x L) ≤ K := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ∑ _x ∈ G, K / N := sum_le_sum fun x hx ↦ hcap x hx
    _ = (G.card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (K / N) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (card_le_card hG).trans_eq (dyadicBlock_card N)) (div_nonneg hK hn.le)
    _ = K := by field_simp

theorem finite_bound {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) (hN : 0 < N)
    (K : ℝ) (hK : 0 ≤ K) (hcap : ∀ x ∈ G, infiniteMarginal x L ≤ K / N) :
    |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
      12 * K / N * CompatibleActivitySplit.absolute L (G.powersetCard 2) + 2 * K ^ 3 / (N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := ThirdRunActivityComparison.repeated_cost_bound G L (K / N) (div_nonneg hK hn.le) hcap
  have hmu := mean_bound hG hN K hcap hK
  calc
    _ ≤ 12 * (K / N) * CompatibleActivitySplit.absolute L (G.powersetCard 2) +
        2 * (K / N) ^ 2 * ∑ x ∈ G, infiniteMarginal x L := hb
    _ ≤ 12 * (K / N) * CompatibleActivitySplit.absolute L (G.powersetCard 2) + 2 * (K / N) ^ 2 * K :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hmu (by positivity))
    _ = _ := by field_simp

theorem uniform_bound (C : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      |RepeatedIndexCost.cost (fun x ↦ infiniteMarginal x L) (infiniteCenteredCoefficient L) G| ≤
        12 * K / N * CompatibleActivitySplit.absolute L (G.powersetCard 2) + 2 * K ^ 3 / (N : ℝ) ^ 2 := by
  obtain ⟨K, hK, NM, hNM⟩ := OriginalWindowFamilyMass.uniform_marginals C
  refine ⟨K, hK, max 1 NM, ?_⟩
  intro N hN L G hband hG
  exact finite_bound hG (by omega) K hK.le (fun x hx ↦ (hNM N (by omega) L x hband (hG hx)).2)

end PaperP1.RepeatedRunCost
