module

public import PaperP1.Coding.PrimeComponentCount
public import PaperP1.Arithmetic.FiniteEvenSquareClasses

/-! # An explicit finite bound on the full value kernel after merging equal values -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteResidualRank

open Finset PaperP1.Arithmetic PaperP1.PinnedGraphResolution PaperP1.PrimeRowComponents
  PaperP1.PrimeComponentCount

local instance residualRankPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance residualRankAdj (S P : Finset ℕ) : DecidableRel (graph S P).Adj := Classical.decRel _

def valueKernel (S : Finset ℕ) : Submodule F₂ (S → F₂) :=
  LinearMap.ker (EvenImage.combination (K := F₂) (FiniteEvenSquareClasses.data S))

theorem kernel_le_rows (S P : Finset ℕ) : valueKernel S ≤ CoverGraphResolution.rowSolutions (rows S P) := by
  intro u hu p
  by_cases hp : p ∈ P
  · simp only [rows, ite_eq_left hp, sum_empty]
  · rw [sum_row p hp]
    have hcoord := congrArg (fun z : ℕ →₀ F₂ ↦ z p) (LinearMap.mem_ker.mp hu)
    rw [EvenImage.combination_apply] at hcoord
    change (∑ n : S, u n • parityVec n.val) p = 0 at hcoord
    simpa only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] using hcoord

theorem kernel_le_graph (S P : Finset ℕ) : valueKernel S ≤ PinnedGraphSpace (graph S P) (pins S P) := by
  intro u hu
  exact CoverGraphResolution.zeroed_mem_graph ⟨kernel_le_rows S P hu, by simp⟩

theorem rank_le_free_components (S P : Finset ℕ) :
    Module.finrank F₂ (valueKernel S) ≤ (unpinnedComponents (graph S P) (pins S P)).card := by
  have h := Submodule.finrank_mono (kernel_le_graph S P)
  rw [finrank_pinnedGraphSpace, card_unpinnedComponents] at h
  exact h

theorem rank_le_small_add_large_budget (S P : Finset ℕ) (K : ℕ) :
    Module.finrank F₂ (valueKernel S) ≤ (small S P K).card + S.card / (K + 1) := by
  have hrank := rank_le_free_components S P
  rw [← small_add_large S P K] at hrank
  exact hrank.trans (Nat.add_le_add_left (large_count S P K) _)

theorem row_rank_eq_free_components {S P : Finset ℕ} (hrows : ∀ p, (rows S P p).card ≤ 2) :
    Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows S P)) =
      (unpinnedComponents (graph S P) (pins S P)).card := by
  rw [rowSolutions_eq_graph hrows, finrank_pinnedGraphSpace, card_unpinnedComponents]

theorem row_rank_le_small_add_large_budget {S P : Finset ℕ} (hrows : ∀ p, (rows S P p).card ≤ 2) (K : ℕ) :
    Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows S P)) ≤ (small S P K).card + S.card / (K + 1) := by
  rw [row_rank_eq_free_components hrows, ← small_add_large S P K]
  exact Nat.add_le_add_left (large_count S P K) _

theorem finite_rank_bound {S P : Finset ℕ} {K U R t : ℕ}
    (hrows : ∀ p, (rows S P p).card ≤ 2)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t) :
    Module.finrank F₂ (valueKernel S) <
      max (P.card + 1) (2 * t * 2 ^ ((P.card + 1) / t + 1)) + S.card / (K + 1) := by
  have hsmall := small_count hrows hlower hupper hR hU hgrowth ht
  have hrank := rank_le_small_add_large_budget S P K
  omega

theorem finite_row_rank_bound {S P : Finset ℕ} {K U R t : ℕ}
    (hrows : ∀ p, (rows S P p).card ≤ 2)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * (K * t)) < U) (ht : 1 ≤ t) :
    Module.finrank F₂ (CoverGraphResolution.rowSolutions (rows S P)) <
      max (P.card + 1) (2 * t * 2 ^ ((P.card + 1) / t + 1)) + S.card / (K + 1) := by
  have hsmall := small_count hrows hlower hupper hR hU hgrowth ht
  have hrank := row_rank_le_small_add_large_budget hrows K
  omega

end PaperP1.FiniteResidualRank
