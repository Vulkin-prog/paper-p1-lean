module

public import PaperP1.Model.WeightedPrimitiveMass
public import PaperP1.Asymptotics.OriginalParticipatingTail
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Primitive rank weights above a fixed large size have an unconditional N^(-1+epsilon) tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedPrimitiveTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.WeightedPrimitiveMass

theorem uniform_tail (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ ConnectedWindowFamilies.Primitive L I) →
      rankMass F L u ≤ (N : ℝ) ^ (-1 + ε) := by
  let M := u * (2 * (2 : ℝ) ^ C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨s, _hs, NT, _hNT, ht⟩ := OriginalParticipatingTail.subcritical_tail C M (2 - ε / 4) (ε / 4)
    hM (by linarith only [hε]) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 s, le_max_left _ _, 10 + NT + NM + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let w := fun x ↦ u * infiniteMarginal x L
  have hw : ∀ x, 0 ≤ w x := fun x ↦ mul_nonneg hu.le (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hcap : ∀ x ∈ dyadicBlock N, w x ≤ M / N := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hu.le
    simpa only [w, M, mul_div_assoc] using h
  have hindep : (∑ I ∈ F, ∏ x ∈ I, w x) ≤ (N : ℝ) ^ (-2 + ε / 2) := by
    have h := ht N (by omega) L hband w hw hcap F (by
      intro I hI
      obtain ⟨hIG, hsize, hprim⟩ := hF I hI
      exact ⟨hIG, (le_max_right 3 s).trans hsize,
        IndependentFullSupportTail.witnesses L I (IndependentFullSupportTail.primitive_fullSupport L I hprim)⟩)
    convert h using 1
    congr 1
    ring
  have hdata : ∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.Nonempty ∧ ConnectedWindowFamilies.Primitive L I := by
    intro I hI
    obtain ⟨hIG, hsize, hprim⟩ := hF I hI
    exact ⟨hIG, card_pos.mp (by have h := le_max_left 3 s; omega), hprim⟩
  calc
    _ ≤ (2 ^ L : ℝ) * ∑ I ∈ F, ∏ x ∈ I, w x := rank_le_independent (by omega) F u hu.le hdata
    _ ≤ ((2 : ℝ) ^ C * N) * (N : ℝ) ^ (-2 + ε / 2) :=
      mul_le_mul (CriticalChannelPowers.word_upper (by omega) hband) hindep
        (sum_nonneg fun I _ ↦ prod_nonneg fun x _ ↦ hw x) (by positivity)
    _ = (2 : ℝ) ^ C * (N : ℝ) ^ (-1 + ε / 2) := by
      conv_rhs =>
        rw [show (-1 : ℝ) + ε / 2 = 1 + (-2 + ε / 2) by ring, Real.rpow_add hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.WeightedPrimitiveTail
