module

public import PaperP1.Asymptotics.UnorderedSeedMassPropagation
public import PaperP1.Asymptotics.CriticalActualMean
public import PaperP1.Model.DependentFactorialBound
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Every fixed actual joint, factorial and ordinary moment is subpolynomial without BCN

These bounds are weaker than uniform boundedness of the fixed moments.
Every order and exponent is selected before the critical threshold.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubpowerFixedCountMoments

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.HeterogeneousDirectMaximum
  PaperP1.FactorialCountMoments

theorem uniform_joint_mass (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ I ∈ G.powersetCard r, infiniteJointMoment L I) ≤ (N : ℝ) ^ ε := by
  by_cases hr : r = 0
  · subst r
    refine ⟨2, le_rfl, ?_⟩
    intro N hN L _ G _
    simpa only [powersetCard_zero, sum_singleton, infiniteJointMoment_empty] using
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) hε.le
  · let δ := ε / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    let M := 2 * (2 : ℝ) ^ C
    have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
    obtain ⟨NP, hp⟩ := UnorderedSeedMassPropagation.uniform_mass 1 (by omega) (r - 1) C δ hδ
    obtain ⟨NM, _hNM, hm⟩ := CriticalActualMean.uniform_bounds C
    obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
    obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((r.factorial : ℝ) * M) δ δ hδ
    refine ⟨max 2 (max NP (max NM (max NG NF))), by omega, ?_⟩
    intro N hN L hband G hG
    have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
    have hsource : (∑ D ∈ G.powersetCard 1, infiniteJointMoment L D) = actualMean G L := by
      rw [SubsetSums.one]
      simp only [InfiniteTripleCancellation.singleton_joint]
      rfl
    have hsource_mem : ∀ D ∈ G.powersetCard 1, D ⊆ dyadicBlock N ∧ D.card = 1 := by
      intro D hD
      obtain ⟨hDG, hcard⟩ := mem_powersetCard.mp hD
      exact ⟨hDG.trans hG, hcard⟩
    have htarget : ∀ I ∈ G.powersetCard r,
        I ⊆ dyadicBlock N ∧ I.card = 1 + (r - 1) ∧ ∃ D ∈ G.powersetCard 1, D ⊆ I := by
      intro I hI
      obtain ⟨hIG, hcard⟩ := mem_powersetCard.mp hI
      obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < I.card)
      exact ⟨hIG.trans hG, by omega, {x},
        mem_powersetCard.mpr ⟨singleton_subset_iff.mpr (hIG hx), by simp⟩,
        singleton_subset_iff.mpr hx⟩
    have hraw := hp N (by omega) L hL hband (G.powersetCard 1) hsource_mem (G.powersetCard r) htarget
    rw [show 1 + (r - 1) = r by omega, hsource] at hraw
    have hmean : actualMean G L ≤ M := by
      calc
        _ ≤ actualMean (dyadicBlock N) L := sum_le_sum_of_subset_of_nonneg hG
          (fun x _ _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
        _ = CountObservables.countMoment (dyadicBlock N) L 1 := actualMean_eq_countMoment (subset_refl _)
        _ ≤ _ := (hm N (by omega) L hband).2
    calc
      _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ δ * actualMean G L := hraw
      _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ δ * M := mul_le_mul_of_nonneg_left hmean (by positivity)
      _ = ((r.factorial : ℝ) * M) * (N : ℝ) ^ δ := by ring
      _ ≤ (N : ℝ) ^ (δ + δ) := hf N (by omega)
      _ = _ := by congr 1; dsimp [δ]; ring

theorem uniform_factorial (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      factorialCountMoment G L r ≤ (N : ℝ) ^ ε := by
  obtain ⟨NJ, _hNJ, hj⟩ := uniform_joint_mass r C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (r.factorial : ℝ) (ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NJ NF), by omega, ?_⟩
  intro N hN L hband G hG
  rw [factorialCountMoment_eq_subset hG]
  calc
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_left (hj N (by omega) L hband G hG) (Nat.cast_nonneg _)
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_ordinary (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CountObservables.countMoment G L r ≤ (N : ℝ) ^ ε := by
  obtain ⟨NF, _hNF, hf⟩ := uniform_factorial r C (ε / 2) (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption
    (((2 * r : ℕ) : ℝ) ^ r + 2 ^ r) (ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NF NA), by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlarge : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hn1 (by positivity)
  have hstatic : (((2 * r : ℕ) : ℝ) ^ r) ≤ (((2 * r : ℕ) : ℝ) ^ r) * (N : ℝ) ^ (ε / 2) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (((2 * r : ℕ) : ℝ) ^ r))
  calc
    _ ≤ (((2 * r : ℕ) : ℝ) ^ r) + 2 ^ r * factorialCountMoment G L r :=
      by simpa only [Nat.cast_pow] using DependentFactorialBound.ordinary_upper (L := L) hG r
    _ ≤ ((((2 * r : ℕ) : ℝ) ^ r) + 2 ^ r) * (N : ℝ) ^ (ε / 2) := by
      have hm := hf N (by omega) L hband G hG
      have hmul := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 2 ^ r)
      nlinarith only [hstatic, hmul]
    _ ≤ (N : ℝ) ^ (ε / 2 + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.SubpowerFixedCountMoments
