module

public import PaperP1.Asymptotics.ComparableSplitProductCount

/-! # Fixed-degree split-product fibres have a uniform subpolynomial count

No height bound on the prescribed kernel is needed. A nonempty fibre
automatically supplies the effective kernel heights used in the proof.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedDegreeKernelCount

open Filter Finset PaperP1.SplitOffsetProducts PaperP1.ComparableSplitProductCount

theorem uniform_count (C : ℕ) (hC : 1 ≤ C) (d : ℕ) (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W q : ℕ, ∀ A : Finset ℤ,
      0 < W → 2 ≤ A.card → A.card ≤ d → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ kernel A n = q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  let c := slack ε
  have hc : 0 < c := slack_pos ε hε
  obtain ⟨NK, hNK⟩ := fixed_kernel_count C hC c D A₀ (ε / 2) hc.le (by positivity)
  obtain ⟨ND, hND⟩ := eventually_atTop.mp (ModerateOrder.loglog_tendsto_atTop.eventually
    (eventually_ge_atTop ((d : ℝ) / c)))
  refine ⟨max 2 (max NK ND), ?_⟩
  intro N hN W q A hW hcard hcardhi hwidth hA S hS
  have hdegree : (A.card : ℝ) ≤ c * Real.log (Real.log N) := by
    have h := (div_le_iff₀ hc).mp (hND N (by omega))
    have hcast : (A.card : ℝ) ≤ d := by exact_mod_cast hcardhi
    nlinarith only [h, hcast]
  have hcount := hNK N (by omega) W q A hW hcard hwidth hdegree hA S hS
  apply hcount.trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  have hslack := slack_log_bound ε hε
  change c * Real.log 2 ≤ ε / 16 at hslack
  linarith

theorem real_interval_count (a b : ℝ) (ha : 0 < a) (d : ℕ) (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W q : ℕ, ∀ A : Finset ℤ,
      0 < W → 2 ≤ A.card → A.card ≤ d → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (∀ u ∈ A, u.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ kernel A n = q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨C, hC, hcomp⟩ := ComparableLogBounds.exists_nat_comparison a b ha
  obtain ⟨N₀, hN₀⟩ := uniform_count C hC d D A₀ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN W q A hW hcard hcardhi hwidth hA S hS
  apply hN₀ N hN W q A hW hcard hcardhi hwidth hA S
  intro n hn
  obtain ⟨hnlo, hnhi, hq⟩ := hS n hn
  exact ⟨(hcomp N n hnlo hnhi).1, (hcomp N n hnlo hnhi).2, hq⟩

end PaperP1.FixedDegreeKernelCount
