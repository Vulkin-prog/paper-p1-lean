module

public import PaperP1.Asymptotics.LogarithmicCoefficientPatterns
public import PaperP1.Asymptotics.CoefficientUnivariateCount
public import PaperP1.Asymptotics.DisjointSquareEquations
public import PaperP1.Combinatorics.FiniteCoverCount
public import PaperP1.Arithmetic.SplitRadicalPointHeight
public import PaperP1.Model.FiniteRademacher

/-! # Two actual one-variable equations on comparable intervals under an upper logarithmic width alone -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicUnivariateCount

open Finset PaperP1.CoefficientSplitRadicalPatterns PaperP1.CriticalCoefficientPatterns
  PaperP1.SplitRadicalPointHeight PaperP1.CoefficientUnivariateCount

theorem uniform_count (a b D ε : ℝ) (K : ℕ) (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin (ε / 2) 2 →
        (∀ d ∈ Q, 0 < d) → ∀ S : Finset ℕ,
          (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ HasSystem L K Q n) → (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NF, hF⟩ := DisjointSquareEquations.two_equations a b ha K D 1 (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hP⟩ := LogarithmicCoefficientPatterns.uniform_pool D (ε / 2) 2 K hD (by positivity)
  refine ⟨max 1 (max NF NP), by omega, ?_⟩
  intro N hN L hwidth Q hQcard hQ S hS
  classical
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let patterns := (pool 2 L K Q).filter Valid
  let hosts := fun q : Pattern 2 ↦ S.filter fun n : ℕ ↦ ∀ i : Fin 2,
    IsSquare (coefficient q i * integerProduct (q.1.1 i) (n : ℤ))
  have hcover : ∀ n ∈ S, ∃ q ∈ patterns, n ∈ hosts q := by
    intro n hn
    obtain ⟨q, hq, hvalid, hroots⟩ := (hS n hn).2.2
    exact ⟨q, mem_filter.mpr ⟨hq, hvalid⟩, mem_filter.mpr ⟨hn, hroots⟩⟩
  have hbound : ∀ q ∈ patterns, ((hosts q).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    intro q hq
    obtain ⟨hqpool, hdisj, hne0, hne1⟩ := mem_filter.mp hq
    have hqdata := (mem_pool 2 L K Q q).mp hqpool
    apply hF N (by omega) (L + 1) (q.1.1 0) (q.1.1 1) (coefficient q 0) (coefficient q 1)
      (by omega) hne0 hne1 hdisj (hqdata.1 0).2 (hqdata.1 1).2
    · simpa only [Real.rpow_one] using hwidth
    · intro z hz
      rcases mem_union.mp hz with hz | hz
      · exact left_bound hqpool 0 z hz
      · exact left_bound hqpool 1 z hz
    · exact (coefficient_pos hQ hqpool 0).ne'
    · exact (coefficient_pos hQ hqpool 1).ne'
    · intro n hn
      obtain ⟨hnS, hnroots⟩ := mem_filter.mp hn
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, hnroots 0, hnroots 1⟩
  have hfinite := FiniteCoverCount.cardinal_le S patterns hosts ((N : ℝ) ^ (ε / 2)) hcover hbound
  have hpatterns : (patterns.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (patterns.card : ℝ) ≤ (pool 2 L K Q).card by exact_mod_cast card_filter_le _ _).trans
      (hP N (by omega) L hwidth Q hQcard)
  calc
    _ ≤ (patterns.card : ℝ) * (N : ℝ) ^ (ε / 2) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hpatterns (Real.rpow_nonneg hNr.le _)
    _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring

end PaperP1.LogarithmicUnivariateCount
