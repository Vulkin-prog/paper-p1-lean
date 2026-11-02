module

public import PaperP1.Asymptotics.AlignedPairRank
public import PaperP1.Asymptotics.BinaryRankPowers
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Model.NormalizedFamilyDefectRank
public import PaperP1.Model.ContactPairMass

/-! # Actual fixed-channel source probabilities include every local and normalized arithmetic defect -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelPairProbability

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.NormalizedUnitCount
  PaperP1.NormalizedPairRankLoss

theorem uniform_bound {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b) (hab : a < b) (hcop : a.Coprime b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → (units a b x y L).Nonempty →
      infiniteJointMoment L {x, y} ≤ (N : ℝ) ^ (-(2 - 1 / (b : ℝ)) + ε) := by
  let α : ℝ := 2 - 1 / (b : ℝ)
  let η := min (ε / 4) (1 / 4)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηq : η ≤ 1 / 4 := min_le_right _ _
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hinv : 1 / (b : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hbR
  have hα : (5 / 3 : ℝ) ≤ α := by dsimp only [α]; linarith only [hinv]
  have hαη : 0 ≤ α - η := by linarith only [hα, hηq]
  have hεη : 0 < ε - η := by linarith only [hηε, hε]
  obtain ⟨NR, hr⟩ := AlignedPairRank.channel_bound C η hη
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max b 2)
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption (BinaryRankPowers.constant C (α - η) η)
    (-α + η) (ε - η) hεη
  refine ⟨max 10 (max NR (max NG NP)), by omega, ?_⟩
  intro N hN L x y hband hx hy hu
  obtain ⟨_hN2, hBmin, hBtwo, _hthin, _hBlo, _hBhi⟩ := hg N (by omega) L hband
  have hL : 0 < L := by omega
  have hbHeight : b ≤ (L + 1) ^ 3 := (show b ≤ L + 1 by omega).trans
    (le_self_pow (by omega) (by decide : 3 ≠ 0))
  have hloss := hr N (by omega) L a b x y hband ha hab.le hcop hbHeight hx hy hu
  let R := Module.finrank F₂ ↥(squareClassSpace x L ⊔ squareClassSpace y L)
  have hdim : 2 * L ≤ R + pairLoss x y L := by unfold pairLoss; dsimp only [R]; omega
  have hdimR : 2 * (L : ℝ) ≤ (R : ℝ) + pairLoss x y L := by exact_mod_cast hdim
  have hR : (α - η) * L - η ≤ (R : ℝ) := by
    dsimp only [α]
    push_cast at hloss
    simp only [div_eq_mul_inv] at hloss ⊢
    nlinarith only [hdimR, hloss]
  have hbinary := BinaryRankPowers.upper (by omega : 2 ≤ N) hαη hband hR
  rw [show -(α - η) = -α + η by ring] at hbinary
  have habsorb : BinaryRankPowers.constant C (α - η) η * (N : ℝ) ^ (-α + η) ≤ (N : ℝ) ^ (-α + ε) := by
    simpa only [show (-α + η) + (ε - η) = -α + ε by ring] using hp N (by omega)
  have hprob := NormalizedFamilyDefectRank.actual_joint_le_rank (ContactPairMass.pair x y) hL
  have hs : FiniteFamilyEnumeration.tupleSet (ContactPairMass.pair x y) = {x, y} := by
    simp [FiniteFamilyEnumeration.tupleSet, ContactPairMass.pair, univ_fin2]
  rw [hs, ContactPairMass.pair_span] at hprob
  exact hprob.trans (hbinary.trans habsorb)

theorem uniform_coarse {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b) (hab : a < b) (hcop : a.Coprime b)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → (units a b x y L).Nonempty →
      infiniteJointMoment L {x, y} ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := uniform_bound ha hb hab hcop C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L x y hband hx hy hunit
  have hinv : 1 / (b : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb)
  exact (hu N hN L x y hband hx hy hunit).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [hinv]))

end PaperP1.FixedChannelPairProbability
