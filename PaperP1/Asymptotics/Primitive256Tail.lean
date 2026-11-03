module

public import PaperP1.Asymptotics.Primitive256RankTail
public import PaperP1.Model.PrimitiveActualMass

/-! # The all-cardinality primitive clause of article 15.12, with power 7/5 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Primitive256Tail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.WeightedPrimitiveMass PaperP1.ConnectedWindowFamilies

theorem uniform_actual (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I) →
      actualMass F L u ≤ (N : ℝ) ^ (-7 / 5 + ε) := by
  obtain ⟨NR, _hNR, hr⟩ := PaperP1.Primitive256RankTail.uniform_strong u C (ε / 2) hu (by positivity)
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C 14 (by norm_num)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    2 (-7 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NR + NF + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hne : ∀ I ∈ F, I.Nonempty := by
    intro I hI
    have hsize := (hF I hI).2.1
    exact card_pos.mp (by omega)
  calc
    _ ≤ 2 * rankMass F L u := PaperP1.PrimitiveActualMass.actual_le_rank F L (by omega) u hu.le hne
    _ ≤ 2 * (N : ℝ) ^ (-7 / 5 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hr N (by omega) L hband F hF) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-7 / 5 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_centered (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I) →
      (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
        (N : ℝ) ^ (-7 / 5 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_actual u C ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hF
  have hmass : (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ actualMass F L u := by
    apply sum_le_sum
    intro I _hI
    exact mul_le_mul_of_nonneg_left
      (by linarith only [infiniteJointMoment_nonneg L I] :
        |infiniteCenteredCoefficient L I| ≤ infiniteJointMoment L I + |infiniteCenteredCoefficient L I|)
      (pow_nonneg hu.le _)
  exact hmass.trans (h N hN L hband F hF)

theorem article_15_12_primitive (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ I ∈ families G L 257, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
        (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_centered u C ε hu hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hstrong := h N hN L hband (families G L 257) (by
    intro I hI
    obtain ⟨hIG, hcard, hprim⟩ := (mem_families G I L 257).mp hI
    exact ⟨hIG.trans hG, by omega, hprim⟩)
  exact hstrong.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))

end PaperP1.Primitive256Tail
