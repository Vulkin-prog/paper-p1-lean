module

public import PaperP1.Combinatorics.OrderedFunctionHosts
public import PaperP1.Asymptotics.OriginalWindowFamilyCounts
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Every fixed-size ordered primitive population has the elementary N^(r/2+epsilon) host budget -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderedPrimitiveHostCount

open Finset PaperP1.ConnectedWindowFamilies PaperP1.FiniteFamilyEnumeration PaperP1.Model

theorem uniform_count (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ S : Finset (Fin r → ℕ),
      (∀ X ∈ S, Function.Injective X ∧ (∀ i, X i ∈ G) ∧ Primitive L (tupleSet X)) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NC, hc⟩ := OriginalWindowFamilyCounts.uniform_hosts r hr C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ)
    ((r : ℝ) / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NC NA), by omega, ?_⟩
  intro N hN L hband G hG S hS
  have hmem : ∀ X ∈ S, Function.Injective X ∧ (∀ i, X i ∈ G) ∧ tupleSet X ∈ primitiveFamilies G L r := by
    intro X hX
    have hh := hS X hX
    refine ⟨hh.1, hh.2.1, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, hh.2.2⟩⟩
    · intro x hx
      obtain ⟨i, _hi, rfl⟩ := mem_image.mp hx
      exact hh.2.1 i
    · rw [tupleSet, card_image_of_injective _ hh.1, card_univ, Fintype.card_fin]
  have hfinite := OrderedFunctionHosts.card_le S G (primitiveFamilies G L r) (filter_subset _ _) hmem
  have hcount := (hc N (by omega) L G hband hG).2
  calc
    _ ≤ (r.factorial : ℝ) * (primitiveFamilies G L r).card := by exact_mod_cast hfinite
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ ((r : ℝ) / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_left hcount (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ (((r : ℝ) / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.OrderedPrimitiveHostCount
