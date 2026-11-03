module

public import PaperP1.Asymptotics.PrimitiveIndependentBudgets
public import PaperP1.Model.PrimitiveRankAmplification

/-! # An unconditional primitive rank tail of power 7/5 at every size at least 256 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Primitive256RankTail

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.WeightedPrimitiveMass PaperP1.ConnectedWindowFamilies

theorem low_nullity (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I ∧
        relativeNullityOn (fun x ↦ squareClassSpace x L) I < 9) →
      rankMass F L u ≤ (N : ℝ) ^ (-7 / 5 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := PaperP1.PrimitiveIndependentBudgets.two_anchor_bound
    u C (ε / 2) hu (by positivity)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    256 (-7 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NB + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hamp : ∀ I ∈ F,
      (2 ^ relativeNullityOn (fun x ↦ squareClassSpace x L) I : ℝ) ≤ 256 := by
    intro I hI
    have hr := (hF I hI).2.2.2
    calc
      _ ≤ (2 : ℝ) ^ 8 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by norm_num
  have hindep := hb N (by omega) L hband F (by
    intro I hI
    exact ⟨(hF I hI).1, (hF I hI).2.1, (hF I hI).2.2.1⟩)
  calc
    _ ≤ 256 * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L :=
      PaperP1.PrimitiveRankAmplification.mass_bound F L u 256 hu.le hamp
    _ ≤ 256 * (N : ℝ) ^ (-7 / 5 + ε / 2) := mul_le_mul_of_nonneg_left hindep (by norm_num)
    _ ≤ (N : ℝ) ^ ((-7 / 5 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem high_nullity (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I ∧
        9 ≤ relativeNullityOn (fun x ↦ squareClassSpace x L) I) →
      rankMass F L u ≤ (N : ℝ) ^ (-5 / 2 + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := PaperP1.PrimitiveIndependentBudgets.ten_anchor_bound
    u C (ε / 2) hu (by positivity)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    ((2 : ℝ) ^ C) (-5 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NB + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hdata : ∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.Nonempty ∧ Primitive L I := by
    intro I hI
    obtain ⟨hIG, hsize, hprim, _hrank⟩ := hF I hI
    exact ⟨hIG, card_pos.mp (by omega), hprim⟩
  have hindep := hb N (by omega) L hband F hF
  have hw : ∀ x, 0 ≤ u * infiniteMarginal x L := fun x ↦
    mul_nonneg hu.le (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  calc
    _ ≤ (2 ^ L : ℝ) * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L :=
      rank_le_independent (by omega) F u hu.le hdata
    _ ≤ ((2 : ℝ) ^ C * N) * (N : ℝ) ^ (-7 / 2 + ε / 2) :=
      mul_le_mul (PaperP1.CriticalChannelPowers.word_upper (by omega) hband) hindep
        (sum_nonneg fun I _ ↦ prod_nonneg fun x _ ↦ hw x) (by positivity)
    _ = (2 : ℝ) ^ C * (N : ℝ) ^ (-5 / 2 + ε / 2) := by
      conv_rhs =>
        rw [show (-5 : ℝ) / 2 + ε / 2 = 1 + (-7 / 2 + ε / 2) by ring,
          Real.rpow_add hn, Real.rpow_one]
      ring
    _ ≤ (N : ℝ) ^ ((-5 / 2 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_strong (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I) →
      rankMass F L u ≤ (N : ℝ) ^ (-7 / 5 + ε) := by
  classical
  obtain ⟨NL, _hNL, hl⟩ := low_nullity u C (ε / 2) hu (by positivity)
  obtain ⟨NH, _hNH, hh⟩ := high_nullity u C (ε / 2) hu (by positivity)
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    2 (-7 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NL + NH + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let FL := F.filter fun I ↦ relativeNullityOn (fun x ↦ squareClassSpace x L) I < 9
  let FH := F.filter fun I ↦ ¬ relativeNullityOn (fun x ↦ squareClassSpace x L) I < 9
  have hlow : rankMass FL L u ≤ (N : ℝ) ^ (-7 / 5 + ε / 2) :=
    hl N (by omega) L hband FL (by
      intro I hI
      obtain ⟨hIF, hr⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, (hF I hIF).2.1, (hF I hIF).2.2, hr⟩)
  have hhigh : rankMass FH L u ≤ (N : ℝ) ^ (-7 / 5 + ε / 2) := by
    have h := hh N (by omega) L hband FH (by
      intro I hI
      obtain ⟨hIF, hr⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, (hF I hIF).2.1, (hF I hIF).2.2, by omega⟩)
    exact h.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  calc
    _ = rankMass FL L u + rankMass FH L u :=
      (sum_filter_add_sum_filter_not F
        (fun I ↦ relativeNullityOn (fun x ↦ squareClassSpace x L) I < 9)
        (fun I ↦ u ^ I.card * PaperP1.PrimitiveWindowMass.weight L I)).symm
    _ ≤ (N : ℝ) ^ (-7 / 5 + ε / 2) + (N : ℝ) ^ (-7 / 5 + ε / 2) := add_le_add hlow hhigh
    _ = 2 * (N : ℝ) ^ (-7 / 5 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-7 / 5 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.Primitive256RankTail
