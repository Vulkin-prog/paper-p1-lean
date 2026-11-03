module

public import PaperP1.Model.OrdinaryIndependentDeficit
public import PaperP1.Asymptotics.OriginalParticipatingMass

/-! # The independent mass of all non-direct original families is at most N^(-1+epsilon) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryIndependentDeficitBound

open Finset PaperP1.Model PaperP1.OrdinaryIndependentDeficit

theorem uniform_bound (C M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ w : ℕ → ℝ, (∀ x, 0 ≤ w x) → (∀ x ∈ dyadicBlock N, w x ≤ M / N) →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → mass G L w ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨NT, _hNT, ht⟩ := OriginalParticipatingMass.uniform_mass C M (ε / 2) hM (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (Real.exp M) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NT + NF, by omega, ?_⟩
  intro N hN L hband w hw hcap G hG
  have hmean : (∑ x ∈ G, w x) ≤ M := by
    calc
      _ ≤ ∑ x ∈ dyadicBlock N, w x := sum_le_sum_of_subset_of_nonneg hG (fun x _ _ ↦ hw x)
      _ ≤ ∑ _x ∈ dyadicBlock N, M / N := sum_le_sum (fun x hx ↦ hcap x hx)
      _ = M := by
        rw [sum_const, nsmul_eq_mul, show (dyadicBlock N).card = N by
          change (Ico N (2 * N)).card = N
          rw [Nat.card_Ico]; omega]
        have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
        field_simp
  have hseeds := ht N (by omega) L hband w hw hcap (seeds G L) (by
    intro I hI
    obtain ⟨hIG, hsize, hwit⟩ := seed_data G L I hI
    exact ⟨hIG.trans hG, hsize, hwit⟩)
  calc
    _ ≤ Real.exp (∑ x ∈ G, w x) * ∑ I ∈ seeds G L, ∏ x ∈ I, w x := finite_bound G L w hw
    _ ≤ Real.exp M * (N : ℝ) ^ (-1 + ε / 2) :=
      mul_le_mul (Real.exp_le_exp.mpr hmean) hseeds
        (sum_nonneg fun I _ ↦ prod_nonneg fun x _ ↦ hw x) (Real.exp_nonneg _)
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.OrdinaryIndependentDeficitBound
