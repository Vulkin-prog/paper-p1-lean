module

public import PaperP1.Arithmetic.PairHostCover
public import PaperP1.Asymptotics.DependentBlockPairsCount
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Arithmetic.OriginalWindowValueBounds
public import PaperP1.Model.RegularSetAsymptotic

/-! # A stronger actual support count in article Proposition 3.2

The full pair rank loss includes local kernels. Covering these separately
extends the effective half-count to every original dyadic pair.
The weighted nonaligned residual is a separate, still open obligation.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalPairHosts

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PairHostCover

def separatedHosts (N L : ℕ) : Finset (ℕ × ℕ) :=
  (hosts N L).filter fun p ↦ p.1 + L < p.2 ∨ p.2 + L < p.1

theorem separated_subset (N L : ℕ) : separatedHosts N L ⊆ hosts N L := filter_subset _ _

theorem effective_hosts (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((DependentBlockPairs.pairs (dyadicBlock N) (blocks L)).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NP, hNP⟩ := DependentBlockPairsCount.article_10_3 (1 / 2) 3 1 C ε
    (by norm_num) (by norm_num) hε
  obtain ⟨NG, hNG⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max NP NG, ?_⟩
  intro N hN L hband
  obtain ⟨hNtwo, _, _, hthin, _, _⟩ := hNG N (by omega) L hband
  have hLN : L ≤ N := by omega
  have hdata := fun x hx ↦ OriginalWindowValueBounds.values_geometry N L x hNtwo
    (mem_Ico.mp hx) hLN
  apply hNP N (by omega) L (dyadicBlock N) (blocks L) hband
  · intro _ x hx v hv
    exact (hdata x hx v hv).1
  · intro _ x hx v hv
    simpa only [one_mul] using
      (show (((v : ℤ) - x).natAbs : ℝ) ≤ (L + 1 : ℕ) by exact_mod_cast (hdata x hx v hv).2)

/-- Unlike the printed separated host count, this bound includes contacts,
equal centres and every locally deficient original window. -/
theorem uniform_count (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((hosts N L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NP, hNP⟩ := effective_hosts C η hη
  obtain ⟨NI, hNI⟩ := RegularSetAsymptotic.irregular_count_critical C η hη
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption 3 (1 + η) η hη
  refine ⟨max 2 (max NP (max NI NF)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := hNP N (by omega) L hband
  have hi := hNI N (by omega) L hband
  have hcover : ((hosts N L).card : ℝ) ≤
      (DependentBlockPairs.pairs (dyadicBlock N) (blocks L)).card +
        2 * (RegularStarts.irregularStarts N L).card * N := by exact_mod_cast card_bound N L
  have hproduct : (N : ℝ) ^ η * N = (N : ℝ) ^ (1 + η) := by
    calc
      _ = (N : ℝ) ^ η * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (η + 1) := (Real.rpow_add hn _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ ≤ 3 * (N : ℝ) ^ (1 + η) := by
      have hmul := mul_le_mul_of_nonneg_right hi hn.le
      rw [hproduct] at hmul
      linarith only [hcover, hp, hmul]
    _ ≤ (N : ℝ) ^ ((1 + η) + η) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

theorem improved_support (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((separatedHosts N L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, _, hN₀⟩ := uniform_count C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  exact (show ((separatedHosts N L).card : ℝ) ≤ (hosts N L).card by
    exact_mod_cast card_le_card (separated_subset N L)).trans (hN₀ N hN L hband)

/-- The complete first displayed count in article 3.2. This does not
assert the separate weighted nonaligned residual estimate. -/
theorem article_3_2_support (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((separatedHosts N L).card : ℝ) ≤ (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨N₀, htwo, hN₀⟩ := uniform_count C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact ((show ((separatedHosts N L).card : ℝ) ≤ (hosts N L).card by
    exact_mod_cast card_le_card (separated_subset N L)).trans (hN₀ N hN L hband)).trans
    (Real.rpow_le_rpow_of_exponent_le hn (by norm_num))

end PaperP1.OriginalPairHosts
