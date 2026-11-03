module

public import PaperP1.Asymptotics.MultiAnchorBudgets
public import PaperP1.Model.PrimitiveAnchorWitnesses
public import PaperP1.Asymptotics.ActualPairRowActivity

/-! # Independent primitive budgets with a fixed anchor rank and cardinality threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveIndependentBudgets

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ConnectedWindowFamilies

theorem uniform_mass (t s : ℕ) (u C A β σ d ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hu : 0 < u) (hA : 1 < A) (hβ : 0 < β) (hβ1 : β < 1)
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hcut : A * (1 - σ) < 1)
    (hgap : (t : ℝ) / A + (1 - β) * (1 - σ) < 1)
    (hmod : d ≤ (t : ℝ) * β - 2 * t / A)
    (hsat : d ≤ (1 - β) * (1 - σ) / 2 * s) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ Primitive L I ∧
        t - 1 ≤ relativeNullityOn (fun x ↦ squareClassSpace x L) I) →
      (∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L) ≤ (N : ℝ) ^ (-d + ε) := by
  let M := u * (2 * (2 : ℝ) ^ C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨NB, _hNB, hb⟩ := PaperP1.MultiAnchorBudgets.uniform_split_bound t C M A β σ (ε / 2)
    htEven ht hM hA hβ hβ1 hσ hσ1 hcut hgap (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := PaperP1.ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NA, ha⟩ := PaperP1.HalfCountSchedule.factor_absorption 2 (-d + ε / 2) (ε / 2)
    (by positivity)
  refine ⟨10 + NB + NM + NA, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let w := fun x ↦ u * infiniteMarginal x L
  have hw : ∀ x, 0 ≤ w x := fun x ↦ mul_nonneg hu.le
    (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hcap : ∀ x ∈ dyadicBlock N, w x ≤ M / N := by
    intro x hx
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hu.le
    simpa only [w, M, mul_div_assoc] using h
  have h := hb N (by omega) L hband w hw hcap s F (by
    intro I hI
    obtain ⟨hIG, hsize, hprim, hdim⟩ := hF I hI
    have hpos : ∀ x ∈ I, 0 < x := by
      intro x hx
      have h := (mem_Ico.mp (hIG hx)).1
      omega
    exact ⟨hIG, hsize, PaperP1.PrimitiveAnchorWitnesses.witnesses
      t L htEven I hprim hpos hdim _ _⟩)
  calc
    _ ≤ (N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε / 2) +
        (N : ℝ) ^ (-(1 - β) * (1 - σ) / 2 * s + ε / 2) := h
    _ ≤ (N : ℝ) ^ (-d + ε / 2) + (N : ℝ) ^ (-d + ε / 2) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hmod]))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hsat]))
    _ = 2 * (N : ℝ) ^ (-d + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-d + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem two_anchor_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I) →
      (∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L) ≤ (N : ℝ) ^ (-7 / 5 + ε) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_mass 2 256 u C 14 (59 / 70) (93 / 100) (7 / 5) ε
    (by decide) (by norm_num) hu (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hF
  have hdata : ∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I ∧
      2 - 1 ≤ relativeNullityOn (fun x ↦ squareClassSpace x L) I := by
    intro I hI
    obtain ⟨hIG, hsize, hprim⟩ := hF I hI
    refine ⟨hIG, hsize, hprim, ?_⟩
    have hpos := hprim.1
    omega
  simpa only [neg_div] using h N hN L hband F hdata

theorem ten_anchor_bound (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 256 ≤ I.card ∧ Primitive L I ∧
        9 ≤ relativeNullityOn (fun x ↦ squareClassSpace x L) I) →
      (∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L) ≤ (N : ℝ) ^ (-7 / 2 + ε) := by
  simpa only [neg_div] using (uniform_mass 10 256 u C 12 (31 / 60) (23 / 25) (7 / 2) ε
    (by decide) (by norm_num) hu (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε)

end PaperP1.PrimitiveIndependentBudgets
