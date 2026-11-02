module

public import PaperP1.Asymptotics.IncompatibleTripleSeed
public import PaperP1.Model.IndependentTargetDeficit
public import PaperP1.Model.InfiniteTripleCancellation
public import PaperP1.Combinatorics.TriplePairIncidence

/-! # Actual incompatible triple activity is bounded by independent mass plus one pair/target deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncompatibleTripleReduction

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.IndependentTargetDeficit
  PaperP1.IncompatibleTripleSeed PaperP1.FamilyIndependentMass

local instance incompatibleTripleReductionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem pair_cost (G : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    (∑ T ∈ families G L, ∑ z ∈ T,
      |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) ≤ deficit G L := by
  rw [incidence_formula]
  apply TriplePairIncidence.restricted_erased_sum_le G 2 (families G L)
    (fun T hT ↦ (mem_filter.mp hT).1)
    (fun e z ↦ |infiniteCenteredCoefficient L e| * infiniteMarginal z L)
    (fun e z ↦ mul_nonneg (abs_nonneg _) (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg z L))
    (fun e z ↦ dependentPair L e ∧ targetDependent L e z)
  intro T hT z hz hn
  obtain ⟨hT, _, hnonzero⟩ := mem_filter.mp hT
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
  have hpT : ∀ x ∈ T, 0 < infiniteMarginal x L := fun x hx ↦ hp x (hsub hx)
  have hc : infiniteCenteredCoefficient L (T.erase z) ≠ 0 := by
    intro hc
    exact hn (by rw [hc, abs_zero, zero_mul])
  have herase : (T.erase z).Nonempty := by
    apply card_pos.mp
    have he := card_erase_add_one hz
    omega
  exact ⟨CenteredDependenceSupport.nullity_pos L hL (T.erase z) herase
    (fun x hx ↦ hpT x (mem_of_mem_erase hx)) hc,
    CenteredDependenceSupport.every_target L hL T hpT hnonzero hz⟩

theorem finite_bound (G : Finset ℕ) (L : ℕ) (hL : 0 < L)
    (hp : ∀ x ∈ G, 0 < infiniteMarginal x L) :
    CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) ≤
      independentMass (families G L) L + deficit G L := by
  rw [activity_eq_active]
  calc
    _ ≤ ∑ T ∈ families G L, ((∏ x ∈ T, infiniteMarginal x L) +
        ∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L) := by
      apply sum_le_sum
      intro T hT
      have hmem := mem_filter.mp hT
      exact InfiniteTripleCancellation.incompatible_set_bound L T
        (mem_powersetCard.mp hmem.1).2 hmem.2.1
    _ = independentMass (families G L) L +
        ∑ T ∈ families G L, ∑ z ∈ T, |infiniteCenteredCoefficient L (T.erase z)| * infiniteMarginal z L :=
      sum_add_distrib
    _ ≤ _ := add_le_add le_rfl (pair_cost G L hL hp)

theorem reduced_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → G ⊆ dyadicBlock N →
      (∀ x ∈ G, 0 < infiniteMarginal x L) →
        CompatibleActivitySplit.incompatibleAbsolute L (G.powersetCard 3) ≤
          (N : ℝ) ^ (-(3 : ℝ) / 2 + ε) + deficit G L := by
  obtain ⟨NM, hNM⟩ := independent_mass C ε hε
  obtain ⟨NL, hNL⟩ := LargeBoundaryTail.critical_parameters C
  refine ⟨max NM NL, ?_⟩
  intro N hN L G hband hG hp
  have hL : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 7) (hNL N (by omega) L hband).2
  exact (finite_bound G L hL hp).trans (add_le_add (hNM N (by omega) L G hband hG hp) le_rfl)

end PaperP1.IncompatibleTripleReduction
