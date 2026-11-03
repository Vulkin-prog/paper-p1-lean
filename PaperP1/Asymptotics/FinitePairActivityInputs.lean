module

public import PaperP1.Asymptotics.SharpPairActivityUnderInputs
public import PaperP1.Asymptotics.SecondCumulantUnderBCN
public import PaperP1.Asymptotics.FinitePairDeficitInputs
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # The complete sharp actual pair and second factorial-cumulant rates under only the existing finite geometric input bundle -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePairActivityInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FinitePairDeficitInputs

theorem uniform_pair (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  obtain ⟨D, k, k₁, k₂, hD, h⟩ := SharpPairActivityUnderInputs.uniform_pair_activity C ε hε
  refine ⟨⟨D, k, k₁, k₂, hD⟩, ?_⟩
  intro hp
  exact h hp.source hp.ordinaryTwo hp.ordinaryThree hp.sourceCurves hp.ordinaryTwoCurves hp.ordinaryThreeCurves

theorem uniform_cumulant (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (1 / 100)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        |RegularCumulantTransfer.secondFactorialCumulant G L| ≤ (N : ℝ) ^ (-2 / 3 + ε) := by
  let K := 2 * (2 : ℝ) ^ C
  obtain ⟨p, hp⟩ := uniform_pair C (ε / 2) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 + K ^ 2) (-2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨NP, _hNP, hp⟩ := hp hgeo
  refine ⟨10 + NM + NF + NP, by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdiag := SecondCumulantUnderBCN.diagonal_bound (by omega : 0 < N) hG
    (fun x hx ↦ hm N (by omega) L hband x (hG hx))
  change (∑ x ∈ G, infiniteMarginal x L ^ 2) ≤ K ^ 2 / N at hdiag
  have hdiagzero : 0 ≤ ∑ x ∈ G, infiniteMarginal x L ^ 2 := sum_nonneg fun x _ ↦ sq_nonneg _
  have hsecond := HeterogeneousRunConversion.second_cumulant_formula (L := L) hG
  change RegularCumulantTransfer.secondFactorialCumulant G L =
    2 * (∑ e ∈ G.powersetCard 2, infiniteCenteredCoefficient L e) - ∑ x ∈ G, infiniteMarginal x L ^ 2 at hsecond
  have hfinite : |RegularCumulantTransfer.secondFactorialCumulant G L| ≤
      2 * (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) + ∑ x ∈ G, infiniteMarginal x L ^ 2 := by
    rw [hsecond]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hdiagzero]
    exact add_le_add (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)) le_rfl
  have hsmall : K ^ 2 / (N : ℝ) ≤ K ^ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hε])) (sq_nonneg K)
  calc
    _ ≤ 2 * (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) + ∑ x ∈ G, infiniteMarginal x L ^ 2 := hfinite
    _ ≤ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) + K ^ 2 * (N : ℝ) ^ (-2 / 3 + ε / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left (hp N (by omega) L hband G hG) (by norm_num)) (hdiag.trans hsmall)
    _ = (2 + K ^ 2) * (N : ℝ) ^ (-2 / 3 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-2 / 3 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FinitePairActivityInputs
