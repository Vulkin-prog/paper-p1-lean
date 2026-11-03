module

public import PaperP1.Model.OriginalTwoAnchorWitnesses
public import PaperP1.Asymptotics.PrimitiveIndependentBudgets

/-! # All connected original families of size at least 256 have independent power 7/5 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedIndependent256Budget

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Connected L I) →
      (∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L) ≤ (N : ℝ) ^ (-7 / 5 + ε) := by
  let M := u * (2 * (2 : ℝ) ^ C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NB, _hNB, hb⟩ := PaperP1.MultiAnchorBudgets.uniform_split_bound
    2 C M 14 (59 / 70) (93 / 100) (ε / 2) (by decide) (by norm_num) hM
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := PaperP1.ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption
    2 (-7 / 5 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NB + NM + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let w := fun x ↦ u * infiniteMarginal x L
  have hw : ∀ x, 0 ≤ w x := fun x ↦ mul_nonneg hu.le
    (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hcap : ∀ x ∈ dyadicBlock N, w x ≤ M / N := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hu.le
    simpa only [w, M, mul_div_assoc] using h
  have h := hb N (by omega) L hband w hw hcap 256 F (by
    intro I hI
    obtain ⟨hIG, hsize, hconn⟩ := hF I hI
    have hpos : ∀ x ∈ I, 0 < x := by
      intro x hx
      have h := (mem_Ico.mp (hIG hx)).1
      omega
    exact ⟨hIG, hsize, PaperP1.OriginalTwoAnchorWitnesses.connected_witnesses L I (by omega) hconn hpos _ _⟩)
  calc
    _ ≤ (N : ℝ) ^ (-(2 : ℝ) * (59 / 70) + 2 * 2 / 14 + ε / 2) +
        (N : ℝ) ^ (-(1 - (59 / 70 : ℝ)) * (1 - 93 / 100) / 2 * 256 + ε / 2) := h
    _ ≤ (N : ℝ) ^ (-7 / 5 + ε / 2) + (N : ℝ) ^ (-7 / 5 + ε / 2) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
    _ = 2 * (N : ℝ) ^ (-7 / 5 + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-7 / 5 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.ConnectedIndependent256Budget
