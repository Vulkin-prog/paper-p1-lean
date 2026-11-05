module

public import PaperP1.Asymptotics.ExpandedAsymmetricDenseMass
public import PaperP1.Asymptotics.AsymmetricCoarseProfile

/-! # A stronger asymmetric weighted bound on an actual N^(1+epsilon) host population

The cardinality is an explicit finite input here. Its application to
actual effective pair/target intersections must prove that input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RestrictedAsymmetricProfile

open Finset PaperP1.Model PaperP1.AsymmetricEvenLoss PaperP1.AsymmetricComponentHostData
  PaperP1.AsymmetricCoarseProfile

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_weight (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (Dold Dcut : ℕ) (hDold : 1 ≤ Dold) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        (2 * Dold + 1) * (L + 1) ≤ H → H ≤ Dcut * (L + 1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x,
        |(n : ℤ) - x| ≤ ((Dold * (L + 1) : ℕ) : ℤ)) →
      ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dold p.1 p.2 L) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (1 + ε / 8) →
      (∑ p ∈ F, weight H L old p) ≤ (N : ℝ) ^ (1 + ε) := by
  let η := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ND, _hND, hD⟩ := ExpandedAsymmetricDenseMass.uniform_weight
    Q hQ C (ε / 2) η Dold Dcut (by positivity) hη
  obtain ⟨NP, hp⟩ := ExpandedAsymmetricKernelPowers.few_components Q C η η Dold Dcut hη.le hη
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max NP (max NF ND)), by omega, ?_⟩
  intro N hN L H hcrit hHlow hHhigh old hold F hF hnon hcard
  let R := Dold * (L + 1)
  have hnew : L + 1 ≤ R := by simpa only [one_mul] using Nat.mul_le_mul_right (L + 1) hDold
  have hamb : 2 * R ≤ H := by dsimp [R]; nlinarith only [hHlow]
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let D := F.filter fun p ↦ η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card
  let S := F \ D
  have hDF : D ⊆ F := filter_subset _ _
  have hSF : S ⊆ F := sdiff_subset
  have hDmass : (∑ p ∈ D, weight H L old p) ≤ (N : ℝ) ^ (1 + ε / 2) := by
    exact (sum_le_sum (fun p _ ↦ sub_le_self _ zero_le_one)).trans
      (hD N (by omega) L H R hcrit le_rfl hnew hamb hHhigh old hold D
        (fun p hpD ↦ hF p (hDF hpD)) (fun p hpD ↦ hnon p (hDF hpD)) (fun _ hpD ↦ (mem_filter.mp hpD).2))
  have hScard : (S.card : ℝ) ≤ 1 * (N : ℝ) ^ (1 + η) := by
    simpa only [one_mul] using (show (S.card : ℝ) ≤ F.card by exact_mod_cast card_le_card hSF).trans hcard
  have hSweight : ∀ p ∈ S, weight H L old p ≤ (N : ℝ) ^ (η + η) := by
    intro p hpS
    obtain ⟨hx, hy⟩ := hF p (hSF hpS)
    have hc : ((nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card : ℝ) ≤ η * ((L + 1 : ℕ) : ℝ) := by
      have hn' : ¬η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 L H R hnew hamb (old p.1)).card :=
        fun hh ↦ (mem_sdiff.mp hpS).2 (mem_filter.mpr ⟨hSF hpS, hh⟩)
      exact (lt_of_not_ge hn').le
    exact (sub_le_self _ zero_le_one).trans (hp N (by omega) L H R hcrit le_rfl hnew hamb hHhigh
      p.1 hx p.2 (ExpandedAsymmetricSupportEnvelope.dyadic_subset_block hQ hy) (old p.1) (hold p.1 hx) hc)
  have hSmass := DenseWeightedSectorUnderInputs.weighted_card_bound S (weight H L old) (N : ℝ)
    1 (1 + η) (η + η) hn hScard hSweight
  rw [one_mul] at hSmass
  have hSmass' : (∑ p ∈ S, weight H L old p) ≤ (N : ℝ) ^ (1 + ε / 2) :=
    hSmass.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η]; linarith only [hε]))
  have hpart := sum_sdiff (f := weight H L old) hDF
  have htotal : (∑ p ∈ F, weight H L old p) ≤ 2 * (N : ℝ) ^ (1 + ε / 2) := by
    change (∑ p ∈ S, weight H L old p) + (∑ p ∈ D, weight H L old p) = _ at hpart
    linarith only [hpart, hDmass, hSmass']
  exact htotal.trans (by simpa only [show (1 + ε / 2) + ε / 2 = 1 + ε by ring] using hf N (by omega))

end PaperP1.RestrictedAsymmetricProfile
