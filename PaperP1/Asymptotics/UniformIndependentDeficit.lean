module

public import PaperP1.Model.IndependentExtensionDeficit
public import PaperP1.Combinatorics.ExceptionalSeedBound
public import PaperP1.Asymptotics.UniformIndependentExposureBudget
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The literal independent deficit, summed over every cardinality, is uniformly at most N^(-1/2+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformIndependentDeficit

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.IndependentExtensionDeficit PaperP1.IndependentExposureEulerBudget

theorem finite_bound {N L : ℕ} (hN : 2 ≤ N) (G S : Finset ℕ)
    (hG : G ⊆ dyadicBlock N) (hS : S ⊆ dyadicBlock N)
    (W : Submodule F₂ (ℕ →₀ F₂))
    (hW : W ≤ ConditionalWindowRank.oldSpan (OldValuePrimeBudget.rawValues S L))
    (u D K : ℝ) (hu : 0 ≤ u) (hD : 0 ≤ D)
    (hmean : (∑ x ∈ dyadicBlock N, (u * infiniteMarginal x L) * windowEuler N L x) ≤ K)
    (hrow : ∀ A ⊆ dyadicBlock N,
      (∑ x ∈ BranchingExceptional.badStarts N L (OldValuePrimeBudget.rawValues (S ∪ A) L),
        u * infiniteMarginal x L) ≤ D * ∏ x ∈ A, windowEuler N L x) :
    deficit G S W L u ≤ D * Real.exp (2 * K) := by
  classical
  rw [deficit_eq_product_weights]
  have hw : ∀ x, 0 ≤ u * infiniteMarginal x L := fun x ↦
    mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have htarget : G \ S ⊆ dyadicBlock N := sdiff_subset.trans hG
  apply ExceptionalSeedBound.constant_bound (G \ S) (families (G \ S) W L)
    (fun A x ↦ x ∈ BranchingExceptional.badStarts N L (OldValuePrimeBudget.rawValues (S ∪ A) L))
    (fun x ↦ u * infiniteMarginal x L) (windowEuler N L) hw (window_one_le N L) D K hD
  · exact (sum_le_sum_of_subset_of_nonneg htarget (fun x _ _ ↦
      mul_nonneg (hw x) (by have h := window_one_le N L x; linarith))).trans hmean
  · intro A hA
    apply le_trans _ (hrow A (hA.trans htarget))
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_filter] at hx
      exact hx.2
    · intro x _ _
      exact hw x
  · intro U hU
    exact ⟨((mem_families (G \ S) W L U).mp hU).1,
      exists_exceptional_seed hN (G \ S) S htarget hS W hW U hU⟩

theorem uniform_bound (s : ℕ) (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ S : Finset ℕ, S ⊆ dyadicBlock N → S.card ≤ s →
      ∀ W : Submodule F₂ (ℕ →₀ F₂), W ≤ ConditionalWindowRank.oldSpan (OldValuePrimeBudget.rawValues S L) →
        deficit G S W L u ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
  let M := u * (2 * (2 : ℝ) ^ C)
  let K := 3 * M * Real.exp 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NB, _hNB, hb⟩ := UniformIndependentExposureBudget.uniform_budget s C M (ε / 2) hM (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (Real.exp (2 * K)) (-1 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + NM + NB + NF, by omega, ?_⟩
  intro N hN L hband G hG S hS hs W hW
  have hcap : ∀ x ∈ dyadicBlock N, u * infiniteMarginal x L ≤ M / N := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hu.le
    simpa only [M, mul_div_assoc] using h
  obtain ⟨hmean, hrow⟩ := hb N (by omega) L hband S hS hs (fun x ↦ u * infiniteMarginal x L) hcap
  calc
    _ ≤ (N : ℝ) ^ (-1 / 2 + ε / 2) * Real.exp (2 * K) :=
      finite_bound (by omega) G S hG hS W hW u _ K hu.le (Real.rpow_nonneg (by positivity) _) hmean hrow
    _ ≤ _ := by
      have h := hf N (by omega)
      rw [show (-1 / 2 + ε / 2) + ε / 2 = -1 / 2 + ε by ring, mul_comm] at h
      exact h

end PaperP1.UniformIndependentDeficit
