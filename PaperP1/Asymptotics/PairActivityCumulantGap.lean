module

public import PaperP1.Model.PairActivityCumulantGap
public import PaperP1.Asymptotics.IncompatiblePairActivity
public import PaperP1.Asymptotics.PositiveSecondCumulant
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Unconditional absolute-pair/cumulant equivalence at the actual moving parameters -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairActivityCumulantGapAsymptotic

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_gap (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      0 ≤ CompatibleActivitySplit.absolute L (G.powersetCard 2) -
        RegularCumulantTransfer.secondFactorialCumulant G L / 2 ∧
      CompatibleActivitySplit.absolute L (G.powersetCard 2) -
        RegularCumulantTransfer.secondFactorialCumulant G L / 2 ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K := 2 * (2 : ℝ) ^ C
  obtain ⟨NI, _hNI, hi⟩ := IncompatiblePairActivityAsymptotic.uniform_activity C δ hδ
  obtain ⟨NP, _hNP, hp⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + K ^ 2 / 2) (-1 + δ) δ hδ
  refine ⟨max 2 (max NI (max NP (max NG NF))), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) hG
    (fun x hx ↦ hp N (by omega) L hband x (hG hx))
  have hd : (∑ x ∈ G, infiniteMarginal x L ^ 2) ≤ K ^ 2 * (N : ℝ) ^ (-1 + δ) := by
    calc
      _ ≤ K ^ 2 / N := hdiag
      _ = K ^ 2 * (N : ℝ) ^ (-(1 : ℝ)) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ])) (sq_nonneg K)
  rw [PairActivityCumulantGap.exact_gap hG hL]
  constructor
  · exact add_nonneg
      (mul_nonneg (by norm_num) (sum_nonneg fun I _ ↦ abs_nonneg (infiniteCenteredCoefficient L I)))
      (div_nonneg (sum_nonneg fun x _ ↦ sq_nonneg (infiniteMarginal x L)) (by norm_num))
  · calc
      _ ≤ (2 + K ^ 2 / 2) * (N : ℝ) ^ (-1 + δ) := by
        have hi' := hi N (by omega) L hband G hG
        nlinarith only [hi', hd]
      _ ≤ (N : ℝ) ^ ((-1 + δ) + δ) := hf N (by omega)
      _ = _ := by congr 1; dsimp [δ]; ring

theorem uniform_relative (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L ∧
      0 ≤ 2 * CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) /
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 1 ∧
      2 * CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2) /
        RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L - 1 ≤
          (N : ℝ) ^ (-1 / 3 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨d, hd, NA, _hNA, ha⟩ := PositiveSecondCumulant.uniform_lower C
  obtain ⟨NE, _hNE, he⟩ := uniform_gap C η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 / d) (-1 / 3 + η) η hη
  refine ⟨max 2 (max NA (max NE (max NG NF))), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by have h := (hg N (by omega) L hband).2.2.1; exact_mod_cast (show 1 ≤ L by omega)
  let α := RegularCumulantTransfer.secondFactorialCumulant (dyadicBlock N) L
  let A := CompatibleActivitySplit.absolute L ((dyadicBlock N).powersetCard 2)
  have hscaled := mul_le_mul_of_nonneg_right hL
    (mul_nonneg hd.le (Real.rpow_nonneg hn.le (-2 / 3)))
  have hlow0 : d * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ d * L * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    nlinarith only [hscaled]
  have hlower : d * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ α := hlow0.trans (ha N (by omega) L hband)
  have hα : 0 < α := (mul_pos hd (Real.rpow_pos_of_pos hn _)).trans_le hlower
  have hgap : 0 ≤ A - α / 2 ∧ A - α / 2 ≤ (N : ℝ) ^ (-1 + η) :=
    he N (by omega) L hband (dyadicBlock N) (subset_refl _)
  have hratio : 2 * A / α - 1 = 2 * (A - α / 2) / α := by field_simp [ne_of_gt hα]
  have hfactor : (2 / d) * (N : ℝ) ^ (-1 / 3 + η) ≤ (N : ℝ) ^ (-1 / 3 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    dsimp [η]
    ring
  refine ⟨hα, ?_, ?_⟩
  · rw [hratio]
    exact div_nonneg (mul_nonneg (by norm_num) hgap.1) hα.le
  · rw [hratio]
    apply (div_le_iff₀ hα).mpr
    have hdd : d * (2 / d) = 2 := by field_simp [ne_of_gt hd]
    calc
      _ ≤ 2 * (N : ℝ) ^ (-1 + η) := mul_le_mul_of_nonneg_left hgap.2 (by norm_num)
      _ = (d * (N : ℝ) ^ (-2 / 3 : ℝ)) * ((2 / d) * (N : ℝ) ^ (-1 / 3 + η)) := by
        rw [show -1 + η = (-2 / 3) + (-1 / 3 + η) by ring,
          Real.rpow_add hn (-2 / 3) (-1 / 3 + η)]
        calc
          _ = (d * (2 / d)) * ((N : ℝ) ^ (-2 / 3 : ℝ) * (N : ℝ) ^ (-1 / 3 + η)) := by rw [hdd]
          _ = _ := by ring
      _ ≤ α * (N : ℝ) ^ (-1 / 3 + ε) :=
        mul_le_mul hlower hfactor (by positivity) hα.le
      _ = _ := mul_comm _ _

end PaperP1.PairActivityCumulantGapAsymptotic
