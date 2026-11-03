module

public import PaperP1.Model.LowTwoPairSeeds
public import PaperP1.Asymptotics.LowTwoPairJointMassUnderInputs
public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Model.CompatibleTripleJointBound

/-! # Low-intersection pair seeds and every fixed compatible extension have the four-thirds scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowTwoPairSeedsUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FinitePairDeficitInputs

theorem uniform_seeds (a C ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 4096)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ LowTwoPairSeeds.families G L a, infiniteJointMoment L I) ≤
          (N : ℝ) ^ (-4 / 3 + a + ε) := by
  obtain ⟨p, hp⟩ := LowTwoPairJointMassUnderInputs.uniform_bound a C ε ha hε
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨N₀, hN₀, hh⟩ := hp hgeo
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG
  exact (LowTwoPairSeeds.mass_bound G L a).trans (hh N hN L hband G hG _
    (fun p hp ↦ (LowTwoPairSeeds.mem_sourcePairs G L a p).mp hp))

theorem uniform_extensions (k : ℕ) (a C ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 16384)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ I.card = 4 + k ∧ ∃ D ∈ LowTwoPairSeeds.families G L a, D ⊆ I) →
        (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-4 / 3 + a + ε) := by
  obtain ⟨p, hp⟩ := uniform_seeds a C (ε / 4) ha (by positivity)
  obtain ⟨NR, hr⟩ := UnorderedSeedMassPropagation.uniform_mass 4 (by decide) k C (ε / 4) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((4 + k).factorial : ℕ) : ℝ)
    (-4 / 3 + a + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 4) / 4096 = ε / 16384 := by ring
  obtain ⟨NS, _hNS, hs⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨4 + NS + NR + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsource := hs N (by omega) L hband G hG
  have hprop := hr N (by omega) L hL hband (LowTwoPairSeeds.families G L a) (by
    intro D hD
    have hd := LowTwoPairSeeds.family_data G L a D hD
    exact ⟨hd.1.trans hG, hd.2.1⟩) F (by
    intro I hI
    obtain ⟨hIG, hcard, hseed⟩ := hF I hI
    exact ⟨hIG.trans hG, hcard, hseed⟩)
  calc
    _ ≤ ((4 + k).factorial : ℝ) * (N : ℝ) ^ (ε / 4) *
        (N : ℝ) ^ (-4 / 3 + a + ε / 4) := hprop.trans
      (mul_le_mul_of_nonneg_left hsource (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)))
    _ = ((4 + k).factorial : ℝ) * (N : ℝ) ^ (-4 / 3 + a + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ ((-4 / 3 + a + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_centered_extensions (k : ℕ) (a C ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 32768)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ I.card = 4 + k ∧ 0 < infiniteJointMoment L I ∧
          ∃ D ∈ LowTwoPairSeeds.families G L a, D ⊆ I) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-4 / 3 + a + ε) := by
  obtain ⟨p, hp⟩ := uniform_extensions k a C (ε / 2) ha (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ (4 + k))
    (-4 / 3 + a + ε / 2) (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 16384 = ε / 32768 := by ring
  obtain ⟨NJ, _hNJ, hj⟩ := hp (by simpa only [hscale] using hgeo)
  refine ⟨4 + NJ + NF + NG, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hmass := hj N (by omega) L hband G hG F (by
    intro I hI
    have hi := hF I hI
    exact ⟨hi.1, hi.2.1, hi.2.2.2⟩)
  calc
    _ ≤ ∑ I ∈ F, (2 : ℝ) ^ (4 + k) * infiniteJointMoment L I := by
      apply sum_le_sum
      intro I hI
      have hi := hF I hI
      simpa only [hi.2.1] using CompatibleTripleJointBound.centered_compatible_bound L I hL hi.2.2.1
    _ = (2 : ℝ) ^ (4 + k) * ∑ I ∈ F, infiniteJointMoment L I := by rw [mul_sum]
    _ ≤ (2 : ℝ) ^ (4 + k) * (N : ℝ) ^ (-4 / 3 + a + ε / 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ (N : ℝ) ^ ((-4 / 3 + a + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_small_intersection_extensions (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p (GeneralGraphHostCount.sizeCap (ε / 65536)) →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ I.card = 4 + k ∧ 0 < infiniteJointMoment L I ∧
          ∃ D ∈ LowTwoPairSeeds.families G L (ε / 2), D ⊆ I) →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  have h := uniform_centered_extensions k (ε / 2) C (ε / 2) (by positivity) (by positivity)
  simpa only [show (ε / 2) / 32768 = ε / 65536 by ring,
    show -4 / 3 + ε / 2 + ε / 2 = -4 / 3 + ε by ring] using h

end PaperP1.LowTwoPairSeedsUnderInputs
