module

public import PaperP1.Asymptotics.CriticalOrderBranching
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # The literal critical branching envelope also pays for excluding every old centre -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CriticalFreshBranchingBudget

open Filter Finset PaperP1.CriticalBranchingBudget PaperP1.Model PaperP1.OldValuePrimeBudget

def orderCap (K : ℝ) (N : ℕ) : ℝ := K * Real.log N / Real.log (Real.log N)

def freshEnvelope (K : ℝ) (N : ℕ) : ℝ := exceptionEnvelope K N + max 0 (orderCap K N)

theorem freshEnvelope_pos (K : ℝ) (N : ℕ) : 0 < freshEnvelope K N :=
  add_pos_of_pos_of_nonneg (Real.exp_pos _) (le_max_left _ _)

theorem envelope_upper (K ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, exceptionEnvelope K N ≤ (N : ℝ) ^ (2 / 3 + ε) := by
  obtain ⟨NL, hl⟩ := eventually_atTop.mp (ModerateOrder.loglog_tendsto_atTop.eventually
    (eventually_ge_atTop (max 1 (errorConstant K / ε))))
  refine ⟨max 3 NL, by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hh := hl N (by omega)
  have hh1 : 1 ≤ Real.log (Real.log N) := (le_max_left _ _).trans hh
  have hhpos : 0 < Real.log (Real.log N) := by linarith only [hh1]
  have hc : errorConstant K ≤ ε * Real.log (Real.log N) :=
    by simpa only [mul_comm] using (div_le_iff₀ hε).mp ((le_max_right _ _).trans hh)
  have hquot : errorConstant K / Real.log (Real.log N) ≤ ε :=
    (div_le_iff₀ hhpos).mpr (by simpa only [mul_comm] using hc)
  have herror : errorConstant K * (Real.log N / Real.log (Real.log N)) ≤ ε * Real.log N := by
    convert mul_le_mul_of_nonneg_right hquot hlog.le using 1; ring
  have hnegative : 0 ≤ Real.log N * Real.log (Real.log (Real.log N)) /
      (9 * Real.log (Real.log N)) := by
    exact div_nonneg (mul_nonneg hlog.le (Real.log_nonneg hh1)) (by positivity)
  rw [Real.rpow_def_of_pos hn]
  apply Real.exp_le_exp.mpr
  unfold rate
  nlinarith only [herror, hnegative]

theorem order_upper (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, orderCap K N ≤ (N : ℝ) ^ ε := by
  obtain ⟨NP, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow K 1 ε hε
  obtain ⟨NL, hl⟩ := eventually_atTop.mp (ModerateOrder.loglog_tendsto_atTop.eventually (eventually_ge_atTop 1))
  refine ⟨max 3 (max NP NL), by omega, ?_⟩
  intro N hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  calc
    _ ≤ K * Real.log N := div_le_self (mul_nonneg hK hlog) (hl N (by omega))
    _ ≤ _ := by simpa only [Real.rpow_one] using hp N (by omega)

theorem fresh_upper (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, freshEnvelope K N ≤ (N : ℝ) ^ (2 / 3 + ε) := by
  obtain ⟨NE, _hNE, he⟩ := envelope_upper K (ε / 2) (by positivity)
  obtain ⟨NO, _hNO, ho⟩ := order_upper K (2 / 3 + ε / 2) hK (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (2 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 3 (max NE (max NO NF)), by omega, ?_⟩
  intro N hN
  have hO : max 0 (orderCap K N) ≤ (N : ℝ) ^ (2 / 3 + ε / 2) :=
    max_le (Real.rpow_nonneg (Nat.cast_nonneg _) _) (ho N (by omega))
  calc
    _ ≤ 2 * (N : ℝ) ^ (2 / 3 + ε / 2) := by
      have hE := he N (by omega)
      unfold freshEnvelope
      linarith only [hE, hO]
    _ ≤ _ := by
      simpa only [show (2 / 3 + ε / 2) + ε / 2 = (2 / 3 : ℝ) + ε by ring] using hf N (by omega)

theorem uniform_small_budget (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, freshEnvelope K N ≤ N ∧
      ∀ m : ℕ, (m : ℝ) ≤ orderCap K N →
        (m : ℝ) * freshEnvelope K N / N ≤ (N : ℝ) ^ (-1 / 3 + ε) := by
  let δ := min (ε / 4) (1 / 12)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ12 : δ ≤ 1 / 12 := min_le_right _ _
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  obtain ⟨NE, _hNE, he⟩ := fresh_upper K δ hK hδ
  obtain ⟨NO, _hNO, ho⟩ := order_upper K δ hK hδ
  refine ⟨max 3 (max NE NO), by omega, ?_⟩
  intro N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hE := he N (by omega)
  refine ⟨hE.trans (by
    calc
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδ12])
      _ = _ := Real.rpow_one _), ?_⟩
  intro m hm
  calc
    _ ≤ ((N : ℝ) ^ δ * (N : ℝ) ^ (2 / 3 + δ)) / N :=
      div_le_div_of_nonneg_right (mul_le_mul (hm.trans (ho N (by omega))) hE
        (freshEnvelope_pos K N).le (Real.rpow_nonneg hn.le _)) hn.le
    _ = (N : ℝ) ^ (-1 / 3 + 2 * δ) := by
      rw [show (-1 / 3 : ℝ) + 2 * δ = (δ + (2 / 3 + δ)) - 1 by ring,
        Real.rpow_sub hn, Real.rpow_one, ← Real.rpow_add hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hδε, hε])

theorem uniform_fresh_exception (K C : ℝ) (hK : 0 ≤ K) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ m : ℕ, (m : ℝ) ≤ orderCap K N →
      ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ m →
        ((A ∪ BranchingExceptional.badStarts N L (rawValues A L)).card : ℝ) ≤ freshEnvelope K N := by
  obtain ⟨N₀, hN₀, hu⟩ := CriticalOrderBranching.uniform_exception_bound K C hK
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN m hm L hband A hA hcard
  have hb := hu N hN m hm L hband A hA hcard
  have hAr : (A.card : ℝ) ≤ m := by exact_mod_cast hcard
  have hAm : (A.card : ℝ) ≤ max 0 (orderCap K N) := hAr.trans (hm.trans (le_max_right _ _))
  have hU : ((A ∪ BranchingExceptional.badStarts N L (rawValues A L)).card : ℝ) ≤
      A.card + (BranchingExceptional.badStarts N L (rawValues A L)).card := by
    exact_mod_cast card_union_le A (BranchingExceptional.badStarts N L (rawValues A L))
  unfold freshEnvelope
  linarith only [hb, hAm, hU]

end PaperP1.CriticalFreshBranchingBudget
