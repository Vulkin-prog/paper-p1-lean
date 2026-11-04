module

public import PaperP1.Asymptotics.AlignedSourcePairMass
public import PaperP1.Model.PairLossWeights
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation

/-! # Height-two boundary pairs and all containing triples have three-halves joint mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeightTwoBoundaryJointMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SourcePairPositiveWeight

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_bound {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) :
    (∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, infiniteJointMoment L e) ≤
      ((2 ^ L : ℝ)⁻¹) ^ 2 * ((∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, setWeight L e) +
        ((BoundaryAlignedPairs.channel N L 1 2).card : ℝ)) := by
  calc
    _ ≤ ∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, ((2 ^ L : ℝ)⁻¹) ^ 2 * (setWeight L e + 1) := by
      apply sum_le_sum
      intro e he
      obtain ⟨x, y, hx, hy, rfl, hxy, _hg⟩ := BoundaryAlignedPairs.data he
      rw [setWeight_pair hxy.ne, weight, sub_add_cancel]
      exact PairLossWeights.joint_bound (by have hh := (mem_Ico.mp hx).1; omega)
        (by have hh := (mem_Ico.mp hy).1; omega) hL
    _ = _ := by rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, infiniteJointMoment L e) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  let η := ε / 4
  let K := ((2 : ℝ) ^ C) ^ 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Nw, _hNw, hw⟩ := AlignedSourcePairMass.uniform_height_two C η hη
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Np, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    CriticalBandScale.upperScale CriticalBandScale.upperScale_pos.le 16 2 η hη
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption (2 * K) (-3 / 2 + η) (ε - η)
    (by dsimp [η]; linarith)
  refine ⟨max 3 (max Nw (max Ng (max Np Nf))), by omega, ?_⟩
  intro N hN L hcrit
  have hgeom := hg N (by omega) L hcrit
  have hL : 0 < L := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpoly : 16 * ((L + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ η := by
    simpa only [Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 16 * (L + 1 : ℝ) ^ 2)] using
      hp N (by omega) L hgeom.2.2.2.2.2
  have hcard : ((BoundaryAlignedPairs.channel N L 1 2).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + η) := by
    calc
      _ ≤ 16 * ((L + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast BoundaryAlignedPairs.height_two_card N L
      _ ≤ (N : ℝ) ^ η := hpoly
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hweights := hw N (by omega) L hcrit
  have hsum : (∑ e ∈ BoundaryAlignedPairs.channel N L 1 2, setWeight L e) +
      ((BoundaryAlignedPairs.channel N L 1 2).card : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 2 + η) := by
    linarith only [hcard, hweights]
  calc
    _ ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (2 * (N : ℝ) ^ (1 / 2 + η)) :=
      (finite_bound (by omega) hL).trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
    _ ≤ (K * (N : ℝ) ^ (-2 : ℝ)) * (2 * (N : ℝ) ^ (1 / 2 + η)) :=
      mul_le_mul_of_nonneg_right (CriticalChannelPowers.nominal_square_upper (by omega) hcrit) (by positivity)
    _ = (2 * K) * (N : ℝ) ^ (-3 / 2 + η) := by
      rw [mul_left_comm, mul_assoc, ← Real.rpow_add hn,
        show (-2 : ℝ) + (1 / 2 + η) = -3 / 2 + η by ring]
      ring
    _ ≤ _ := by
      simpa only [show (-3 / 2 + η) + (ε - η) = -3 / 2 + ε by ring] using hf N (by omega)

theorem uniform_triples (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ dyadicBlock N ∧ T.card = 3 ∧
        ∃ e ∈ BoundaryAlignedPairs.channel N L 1 2, e ⊆ T) →
      (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨Nm, _hNm, hm⟩ := uniform_mass C (ε / 4) (by positivity)
  obtain ⟨Nr, hr⟩ := UnorderedSeedMassPropagation.uniform_mass 2 (by decide) 1 C (ε / 4) (by positivity)
  obtain ⟨Ng, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 6 (-3 / 2 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max Nm (max Nr (max Ng Nf))), by omega, ?_⟩
  intro N hN L hcrit F hF
  have hL : 0 < L := by have hh := (hg N (by omega) L hcrit).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprop := hr N (by omega) L hL hcrit (BoundaryAlignedPairs.channel N L 1 2)
    (fun _ he ↦ mem_powersetCard.mp (mem_filter.mp he).1) F hF
  have hmass := hm N (by omega) L hcrit
  calc
    _ ≤ (6 : ℝ) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-3 / 2 + ε / 4) :=
      hprop.trans (mul_le_mul_of_nonneg_left hmass (by norm_num; positivity))
    _ = 6 * (N : ℝ) ^ (-3 / 2 + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add hn, show ε / 4 + (-3 / 2 + ε / 4) = -3 / 2 + ε / 2 by ring]
    _ ≤ _ := by
      simpa only [show (-3 / 2 + ε / 2) + ε / 2 = -3 / 2 + ε by ring] using hf N (by omega)

end PaperP1.HeightTwoBoundaryJointMass
