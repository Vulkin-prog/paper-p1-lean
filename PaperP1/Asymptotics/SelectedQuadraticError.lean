module

public import PaperP1.Arithmetic.SelectedQuadraticBudget
public import PaperP1.Asymptotics.SplitOffsetHeightBudget

/-! # Uniform absorption of the actual selected-quadratic resultant error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedQuadraticError

open Finset PaperP1.SplitOffsetProducts PaperP1.SelectedQuadraticBudget

theorem resultant_error_budget (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ,
      0 < W → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      4 * Real.log (resultant A) / ((A.card : ℝ) / 2) ≤ ε * Real.log N := by
  let K : ℝ := |Real.log (2 * D) + A₀| + 1
  let E : ℝ := 8 * c * K
  obtain ⟨Ne, hNe⟩ := PaperP1.GrowingDegreePrimeError.polylog_error_budget E ε hε
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually (Filter.eventually_ge_atTop 1))
  refine ⟨max 2 (max Ne Nl), ?_⟩
  intro N hN W A hW hcard hwidth hdegree hA
  have hNtwo : 2 ≤ N := by omega
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll := hNl N (by omega)
  have hllpos : 0 < Real.log (Real.log N) := by linarith
  have hd : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hwlog := PaperP1.SplitOffsetHeightBudget.width_log_bound D A₀ hD N W hNtwo hW hll hwidth
  have hwK : Real.log (2 * W : ℝ) ≤ K * Real.log (Real.log N) := by
    have hconst : Real.log (2 * D) + A₀ ≤ K := by dsimp [K]; linarith [le_abs_self (Real.log (2 * D) + A₀)]
    exact hwlog.trans (mul_le_mul_of_nonneg_right hconst hllpos.le)
  have hres := resultant_le_pow A W hW hA
  have hresR : (resultant A : ℝ) ≤ (2 * (W : ℝ)) ^ (A.card ^ 2) := by exact_mod_cast hres
  have hreslog := Real.log_le_log (by exact_mod_cast resultant_pos A : (0 : ℝ) < resultant A) hresR
  rw [Real.log_pow] at hreslog
  push_cast at hreslog
  have hdiv : Real.log (resultant A) / (A.card : ℝ) ≤ (A.card : ℝ) * Real.log (2 * W : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hreslog]
  have hlogW : 0 ≤ Real.log (2 * W : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * W by omega))
  have hproduct := mul_le_mul hdegree hwK hlogW (mul_nonneg hc hllpos.le)
  have he := hNe N (by omega)
  have heN : E * (Real.log (Real.log N)) ^ 2 ≤ ε * Real.log N := by
    by_contra hnot
    have hstrict := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hllpos
    nlinarith only [he, hstrict]
  have hid : 4 * Real.log (resultant A) / ((A.card : ℝ) / 2) =
      8 * (Real.log (resultant A) / (A.card : ℝ)) := by ring
  rw [hid]
  dsimp [E] at heN
  nlinarith only [hdiv, hproduct, heN]

theorem source_fixed_pair_selection (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W e : ℕ, ∀ A : Finset ℤ, ∀ P : Finset (Finset ℤ),
      N ≤ n → 0 < W → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → e ∣ kernel A n →
      Set.PairwiseDisjoint (P : Set (Finset ℤ)) id → P.biUnion id = A → (∀ B ∈ P, B.card = 2) →
      ∃ B ∈ P, weight (PaperP1.SquarefreeOutsideDivisor.outside e (resultant A)) n B / Real.log N ≤
        (Real.log (kernel A n) / Real.log N - 2 * Real.log e / Real.log N) / ((A.card : ℝ) / 2) + ε := by
  obtain ⟨Ne, hNe⟩ := resultant_error_budget c D A₀ ε hc hD hε
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D) A₀ 1 (by norm_num)
  refine ⟨max 2 (max Ne Nw), ?_⟩
  intro N hN n W e A P hnlo hW hcard hwidth hdegree hA he hdis hunion hpairs
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hd : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  have hWNr : (2 * W : ℝ) ≤ N := by
    have hb := hNw N (by omega)
    rw [Real.rpow_one] at hb
    nlinarith
  have hWN : 2 * W ≤ N := by exact_mod_cast hWNr
  have hWn : W < n := by omega
  have hvalues : ∀ a ∈ A, (n : ℤ) + a ≠ 0 := fun a ha ↦ (factor_pos A n W hWn hA a ha).ne'
  have hcardP := PaperP1.FinitePairPartition.partition_cardinality A P hdis hunion hpairs
  have hP : P.Nonempty := card_pos.mp (by omega)
  have hvalues' : ∀ a ∈ P.biUnion id, (n : ℤ) + a ≠ 0 := by rwa [hunion]
  have he' : e ∣ kernel (P.biUnion id) n := by rwa [hunion]
  obtain ⟨B, hB, hb⟩ := selected_source_block P hP e n hdis hvalues' he'
  rw [hunion] at hb
  have hcP : (P.card : ℝ) = (A.card : ℝ) / 2 := by
    have hr : (A.card : ℝ) = 2 * (P.card : ℝ) := by exact_mod_cast hcardP
    linarith
  rw [hcP] at hb
  have herror := hNe N (by omega) W A hW hcard hwidth hdegree hA
  refine ⟨B, hB, (div_le_iff₀ hl).mpr ?_⟩
  have hsum : weight (PaperP1.SquarefreeOutsideDivisor.outside e (resultant A)) n B ≤
      (Real.log (kernel A n) - 2 * Real.log e) / ((A.card : ℝ) / 2) + ε * Real.log N := by
    apply hb.trans
    rw [add_div]
    exact add_le_add le_rfl herror
  have hid : ((Real.log (kernel A n) / Real.log N - 2 * Real.log e / Real.log N) /
      ((A.card : ℝ) / 2) + ε) * Real.log N =
      (Real.log (kernel A n) - 2 * Real.log e) / ((A.card : ℝ) / 2) + ε * Real.log N := by
    field_simp
  rw [hid]
  exact hsum

theorem source_selected_pair (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W e : ℕ, ∀ A : Finset ℤ,
      N ≤ n → 0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → e ∣ kernel A n →
      ∃ P : Finset (Finset ℤ), Set.PairwiseDisjoint (P : Set (Finset ℤ)) id ∧
        P.biUnion id = A ∧ (∀ B ∈ P, B.card = 2) ∧
        ∃ B ∈ P, weight (PaperP1.SquarefreeOutsideDivisor.outside e (resultant A)) n B / Real.log N ≤
          (Real.log (kernel A n) / Real.log N - 2 * Real.log e / Real.log N) / ((A.card : ℝ) / 2) + ε := by
  obtain ⟨N₀, hN₀⟩ := source_fixed_pair_selection c D A₀ ε hc hD hε
  refine ⟨N₀, ?_⟩
  intro N hN n W e A hnlo hW heven hcard hwidth hdegree hA he
  obtain ⟨P, hdis, hunion, hpairs⟩ := PaperP1.FinitePairPartition.exists_pair_partition A heven
  obtain ⟨B, hB, hbudget⟩ := hN₀ N hN n W e A P hnlo hW hcard hwidth hdegree hA he hdis hunion hpairs
  exact ⟨P, hdis, hunion, hpairs, B, hB, hbudget⟩

end PaperP1.SelectedQuadraticError
