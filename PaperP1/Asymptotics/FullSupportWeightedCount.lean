module

public import PaperP1.Model.FullSupportOrderedLists
public import PaperP1.Asymptotics.OriginalParticipatingMass

/-! # Companion T22.1, with the stronger N^(-1+epsilon) bound for every cutoff at least two -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullSupportWeightedCount

open Finset PaperP1.Model PaperP1.FullSupportOrderedLists

theorem uniform_ordered_mass (C u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ∀ s : ℕ, 2 ≤ s → orderedMass G L s (u * (2 ^ L : ℝ)⁻¹) ≤ (N : ℝ) ^ (-1 + ε) := by
  let M := u * (2 : ℝ) ^ C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨N₀, hN₀, hm⟩ := OriginalParticipatingMass.uniform_mass C M ε hM hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG s hs
  have hcap : ∀ x ∈ dyadicBlock N, u * (2 ^ L : ℝ)⁻¹ ≤ M / N := by
    intro _ _
    calc
      _ ≤ u * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left
        (LocalRigidityConsequences.nominal_marginal_bound (by omega) hband) hu.le
      _ = _ := by dsimp [M]; ring
  have hmass := hm N hN L hband (fun _ ↦ u * (2 ^ L : ℝ)⁻¹) (fun _ ↦ by positivity)
    hcap (IndependentFullSupportTail.families G L s) (by
      intro I hI
      obtain ⟨hIG, hsize, hfull⟩ := (IndependentFullSupportTail.mem_families G I L s).mp hI
      exact ⟨hIG.trans hG, hs.trans hsize, IndependentFullSupportTail.witnesses L I hfull⟩)
  rw [ordered_mass_eq]
  simpa only [prod_const] using hmass

theorem full_list_bound (s : ℕ) (hs : 2 ≤ s) (C u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ r ∈ Icc s G.card, (u ^ r / (r.factorial : ℝ)) *
        ((lists G L r).card * ((2 ^ L : ℝ)⁻¹) ^ r)) ≤
          (N : ℝ) ^ (-2 * (s : ℝ) / (2 * s + 1) + ε) := by
  obtain ⟨N₀, hN₀, hm⟩ := uniform_ordered_mass C u ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  rw [← nominal_weight_formula]
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hratio : 2 * (s : ℝ) / (2 * s + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  exact (hm N hN L hband G hG s hs).trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by
      rw [show -2 * (s : ℝ) / (2 * s + 1) = -(2 * (s : ℝ) / (2 * s + 1)) by ring]
      linarith only [hratio]))

theorem companion_T22_1 (s : ℕ) (hs : 2 ≤ s) (C u ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ r ∈ Icc s G.card, (u ^ r / (r.factorial : ℝ)) *
        ((manuscriptLists G L r).card * ((2 ^ L : ℝ)⁻¹) ^ r)) ≤
          (N : ℝ) ^ (-2 * (s : ℝ) / (2 * s + 1) + ε) := by
  obtain ⟨N₀, hN₀, hm⟩ := full_list_bound s hs C u ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  apply le_trans _ (hm N hN L hband G hG)
  apply sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_le_card (manuscriptLists_subset G L r)) (by positivity)) (by positivity)

end PaperP1.FullSupportWeightedCount
