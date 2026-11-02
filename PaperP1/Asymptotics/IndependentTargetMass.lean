module

public import PaperP1.Model.WindowTargetHosts
public import PaperP1.Model.CompatibleActivitySplit
public import PaperP1.Asymptotics.EffectiveHalfCount
public import PaperP1.Asymptotics.OriginalWindowFamilyMass
public import Mathlib.Tactic.FieldSimp

/-! # Fixed-source actual dependent targets have independent mass N^(-1/2+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentTargetMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.WindowTargetHosts

theorem uniform_count (s : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G e : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      e ⊆ G → e.card = s →
        ((targets G L e).card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NC, hNC⟩ := EffectiveHalfCount.critical_centre_count 1 s 1 2 1 C ε
    (by norm_num) (by norm_num) hε
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max NC NG, ?_⟩
  intro N hN L G e hband hG heG he
  obtain ⟨hNtwo, _, _, hthin, _, _⟩ := hNG N (by omega) L hband
  have hL : L ≤ N := by omega
  let old := FiniteFamilyEnumeration.centres e he
  let oldBlocks := fun i : Fin s ↦ NormalizedWindowSets.values (old i) L
  have holdG : ∀ i, old i ∈ G := FiniteFamilyEnumeration.centres_mem G e he heG
  have hheight : ∀ x ∈ G, (1 : ℝ) * N ≤ x ∧ (x : ℝ) ≤ 2 * N := by
    intro x hx
    obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp (hG hx)
    constructor
    · simpa only [one_mul] using (show (N : ℝ) ≤ x by exact_mod_cast hxlo)
    · exact_mod_cast hxhi.le
  have hdist : ∀ x ∈ G, ∀ v ∈ NormalizedWindowSets.values x L,
      (((v : ℤ) - x).natAbs : ℝ) ≤ (1 : ℝ) * (L + 1 : ℕ) := by
    intro x hx v hv
    simpa only [one_mul] using (show (((v : ℤ) - x).natAbs : ℝ) ≤ (L + 1 : ℕ) by
      exact_mod_cast (OriginalWindowValueBounds.values_geometry N L x hNtwo (mem_Ico.mp (hG hx)) hL v hv).2)
  have hcount := hNC N (by omega) L old G (blocks L) oldBlocks hband hheight
    (fun i ↦ hheight _ (holdG i)) (fun _ x hx v hv ↦ hdist x hx v hv)
    (fun i v hv ↦ hdist _ (holdG i) v hv)
  have hvalues : sourceValues L e = univ.biUnion oldBlocks := sourceValues_enumeration L e he
  have hle : ((targets G L e).card : ℝ) ≤
      (EffectiveWindowLists.lists G (blocks L) (sourceValues L e)).card := by
    exact_mod_cast card_le_lists G L e
  rw [hvalues] at hle
  exact hle.trans (by simpa only [Nat.cast_one] using hcount)

theorem uniform_mass (s : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G e : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      e ⊆ G → e.card = s →
        (∑ z ∈ targets G L e, infiniteMarginal z L) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NC, hNC⟩ := uniform_count s C (ε / 2) (by positivity)
  obtain ⟨K, hK, NM, hNM⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption K (-(1 : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NM NF)), ?_⟩
  intro N hN L G e hband hG heG he
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hNC N (by omega) L G e hband hG heG he
  have hproduct : (N : ℝ) ^ ((1 : ℝ) / 2 + ε / 2) * (K / N) =
      K * (N : ℝ) ^ (-(1 : ℝ) / 2 + ε / 2) := by
    rw [show (1 : ℝ) / 2 + ε / 2 = (-(1 : ℝ) / 2 + ε / 2) + 1 by ring,
      Real.rpow_add hn, Real.rpow_one]
    field_simp
  calc
    _ ≤ ∑ _z ∈ targets G L e, K / N := by
      apply sum_le_sum
      intro z hz
      exact (hNM N (by omega) L z hband (hG (mem_sdiff.mp (mem_filter.mp hz).1).1)).2
    _ = ((targets G L e).card : ℝ) * (K / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + ε / 2) * (K / N) :=
      mul_le_mul_of_nonneg_right hcount (div_nonneg hK.le hn.le)
    _ = K * (N : ℝ) ^ (-(1 : ℝ) / 2 + ε / 2) := hproduct
    _ ≤ (N : ℝ) ^ (-(1 : ℝ) / 2 + ε / 2 + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; ring

theorem deficit_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
        IndependentTargetDeficit.deficit G L ≤
          CompatibleActivitySplit.absolute L (G.powersetCard 2) * (N : ℝ) ^ (-(1 : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NM, hNM⟩ := uniform_mass 2 C ε hε
  refine ⟨NM, ?_⟩
  intro N hN L G hband hG
  unfold IndependentTargetDeficit.deficit CompatibleActivitySplit.absolute
  rw [sum_mul]
  calc
    _ ≤ ∑ e ∈ (G.powersetCard 2).filter (IndependentTargetDeficit.dependentPair L),
        |infiniteCenteredCoefficient L e| * (N : ℝ) ^ (-(1 : ℝ) / 2 + ε) := by
      apply sum_le_sum
      intro e he
      obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp (mem_filter.mp he).1
      exact mul_le_mul_of_nonneg_left (hNM N hN L G e hband hG hesub hecard) (abs_nonneg _)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun e _ _ ↦ mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))

end PaperP1.IndependentTargetMass
