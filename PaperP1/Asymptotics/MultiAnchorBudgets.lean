module

public import PaperP1.Asymptotics.MultiAnchorModerateMass
public import PaperP1.Asymptotics.MultiAnchorSaturatedMass

/-! # Both literal certificate budgets of article Lemma 15.11 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorBudgets

open Finset PaperP1.Model PaperP1.MultiAnchorFamilyMass PaperP1.MultiAnchorRelationFamilies

def moderate (t B N : ℕ) (Y T : ℝ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) := by
  classical
  exact F.filter fun I ↦ Certified t I.card B N Y T I

def saturated (t B N : ℕ) (Y T : ℝ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) := by
  classical
  exact F.filter fun I ↦ ¬ Certified t I.card B N Y T I

theorem article_15_11 (t : ℕ) (C M A β σ ε : ℝ) (_htEven : Even t) (ht : 2 ≤ t)
    (hM : 0 ≤ M) (hA : 1 < A) (hβ : 0 < β) (hβ1 : β < 1)
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hcut : A * (1 - σ) < 1)
    (hgap : (t : ℝ) / A + (1 - β) * (1 - σ) < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ s : ℕ, ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧
        Witnesses t (L + 1) ((Real.log N) ^ A) ((N : ℝ) ^ β) I) →
      (∑ I ∈ moderate t (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) F, ∏ x ∈ I, p x) ≤
        (N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε) ∧
      (∑ I ∈ saturated t (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) F, ∏ x ∈ I, p x) ≤
        (N : ℝ) ^ (-(1 - β) * (1 - σ) / 2 * s + ε) := by
  classical
  obtain ⟨NM, _hNM, hm⟩ := PaperP1.MultiAnchorModerateMass.uniform_bound t C M A β ε
    (by omega) hM hA hβ.le hε
  obtain ⟨NS, _hNS, hs⟩ := PaperP1.MultiAnchorSaturatedMass.uniform_bound t C M A β σ ε
    (by omega) hM hA hβ.le hβ1 hσ.le hσ1 hcut hgap hε
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C A hA
  refine ⟨10 + NM + NS + NF, by omega, ?_⟩
  intro N hN L hband p hp hcap s F hF
  have hY := (hf N (by omega) L hband).2.2.2.1
  constructor
  · apply hm N (by omega) L hband p hp hcap
    intro I hI
    obtain ⟨hIF, hcert⟩ := mem_filter.mp hI
    exact ⟨(hF I hIF).1, hcert⟩
  · apply hs N (by omega) L hband p hp hcap s
    intro I hI
    obtain ⟨hIF, hnot⟩ := mem_filter.mp hI
    obtain ⟨hIG, hcard, hw⟩ := hF I hIF
    exact ⟨hIG, hcard, noncertified_admissible I hIG _ _ hY hw hnot⟩

theorem uniform_split_bound (t : ℕ) (C M A β σ ε : ℝ) (htEven : Even t) (ht : 2 ≤ t)
    (hM : 0 ≤ M) (hA : 1 < A) (hβ : 0 < β) (hβ1 : β < 1)
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hcut : A * (1 - σ) < 1)
    (hgap : (t : ℝ) / A + (1 - β) * (1 - σ) < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ s : ℕ, ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧
        Witnesses t (L + 1) ((Real.log N) ^ A) ((N : ℝ) ^ β) I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤
        (N : ℝ) ^ (-(t : ℝ) * β + 2 * t / A + ε) +
          (N : ℝ) ^ (-(1 - β) * (1 - σ) / 2 * s + ε) := by
  classical
  obtain ⟨N₀, hN₀, h⟩ := article_15_11 t C M A β σ ε htEven ht hM hA hβ hβ1 hσ hσ1 hcut hgap hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband p hp hcap s F hF
  obtain ⟨hm, hs⟩ := h N hN L hband p hp hcap s F hF
  calc
    _ = (∑ I ∈ moderate t (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) F, ∏ x ∈ I, p x) +
        ∑ I ∈ saturated t (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) F, ∏ x ∈ I, p x :=
      (sum_filter_add_sum_filter_not F
        (fun I ↦ Certified t I.card (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) I) _).symm
    _ ≤ _ := add_le_add hm hs

end PaperP1.MultiAnchorBudgets
