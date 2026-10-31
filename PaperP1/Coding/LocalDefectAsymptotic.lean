module

public import PaperP1.Coding.LocalDefectRadius

@[expose] public section

/-! # Uniform local defect bounds throughout logarithmic windows -/

namespace PaperP1.LocalDefectAsymptotic

open Finset LocalDefectBound LocalDefectRate LocalDefectRadius

theorem card_mono_width {H U R S : ℕ} (hRS : R ≤ S) :
    (defectsInInterval H U R).card ≤ (defectsInInterval H U S).card := by
  apply card_le_card
  intro n hn
  obtain ⟨hUn, hnR, hdef⟩ := mem_defectsInInterval.mp hn
  exact mem_defectsInInterval.mpr ⟨hUn, by omega, hdef⟩

/-- A common threshold and constant for every actual interval of logarithmic
width in a fixed positive macroscopic range. No lower bound on H is needed. -/
theorem local_defect_count_le_log_div_loglog_eventually
    (c C D E : ℝ) (hc : 0 < c) (hC : 0 < C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H U R : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (R : ℝ) ≤ E * Real.log N →
      c * N ≤ (U : ℝ) → (U : ℝ) ≤ C * N →
      ((defectsInInterval H U R).card : ℝ) ≤
        K * Real.log N / Real.log (Real.log N) := by
  let A : ℕ := budgetConstant D
  let S : ℝ := 4096 + 2 * |Real.log c| + |Real.log C| +
    64 * (E + 2) + 8 * (E + 2) / c
  obtain ⟨Ncore, hNcore⟩ := exists_nat_gt (Real.exp S)
  refine ⟨((2 * 2 ^ (A + 1) : ℕ) : ℝ), by positivity, max Ncore 2, ?_⟩
  intro N hN H U R hH hR hUlo hUhi
  let s : ℝ := Real.log N
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hexp : Real.exp S < (N : ℝ) :=
    hNcore.trans_le (by exact_mod_cast (le_max_left Ncore 2).trans hN)
  have hlarge : S ≤ s := by
    have h := Real.log_lt_log (Real.exp_pos S) hexp
    exact (by simpa only [Real.log_exp] using h.le)
  have hS :
      4096 + 2 * |Real.log c| + |Real.log C| +
        64 * (E + 2) + 8 * (E + 2) / c ≤ s := hlarge
  have hgeom0 : 0 ≤ 64 * (E + 2) := by positivity
  have hmove0 : 0 ≤ 8 * (E + 2) / c := by positivity
  have hs : 4096 ≤ s := by
    linarith [abs_nonneg (Real.log c), abs_nonneg (Real.log C)]
  have hspos : 0 < s := by linarith
  have hs0 : 0 ≤ s := hspos.le
  have hlogs : 0 < Real.log s := Real.log_pos (by linarith)
  have hsc : -2 * Real.log c ≤ s := by
    linarith [neg_le_abs (Real.log c), abs_nonneg (Real.log C)]
  have hsC : Real.log C ≤ s := by
    linarith [le_abs_self (Real.log C), abs_nonneg (Real.log c)]
  have hsgeom : 64 * (E + 2) ≤ s := by
    linarith [abs_nonneg (Real.log c), abs_nonneg (Real.log C)]
  have hsmove : 8 * (E + 2) / c ≤ s := by
    linarith [abs_nonneg (Real.log c), abs_nonneg (Real.log C)]
  have hUpos : (0 : ℝ) < U := (mul_pos hc hNpos).trans_le hUlo
  have hlogUlo : s / 2 ≤ Real.log (U : ℝ) := by
    have h := Real.log_le_log (mul_pos hc hNpos) hUlo
    rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hNpos)] at h
    dsimp [s] at hsc ⊢
    linarith
  have hlogUhi : Real.log (U : ℝ) ≤ 2 * s := by
    have h := Real.log_le_log hUpos hUhi
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt hNpos)] at h
    dsimp [s] at hsC ⊢
    linarith
  let Rbar : ℕ := ⌈(E + 1) * s⌉₊
  have hceil : (E + 1) * s ≤ (Rbar : ℝ) := Nat.le_ceil _
  have hEs : 0 ≤ E * s := mul_nonneg hE hs0
  have hbarlo : s ≤ (Rbar : ℝ) := by nlinarith
  have hbarhi : (Rbar : ℝ) ≤ (E + 2) * s := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (E + 1) * s by positivity)
    change (Rbar : ℝ) < (E + 1) * s + 1 at h
    nlinarith
  have hRbar : R ≤ Rbar := by
    have hle : (R : ℝ) ≤ Rbar := by
      calc
        _ ≤ E * s := hR
        _ ≤ (E + 1) * s := by nlinarith
        _ ≤ Rbar := hceil
    exact_mod_cast hle
  have hbarOne : 1 ≤ Rbar := by exact_mod_cast (show (1 : ℝ) ≤ Rbar by linarith)
  have hbarlogpos : 0 < Real.log (64 * (Rbar : ℝ)) := by
    apply Real.log_pos
    have hbarOneReal : (1 : ℝ) ≤ Rbar := by exact_mod_cast hbarOne
    linarith
  have hbarloglo : Real.log s ≤ Real.log (64 * (Rbar : ℝ)) := by
    apply Real.log_le_log hspos
    nlinarith
  have hbarloghi : Real.log (64 * (Rbar : ℝ)) ≤ 2 * Real.log s := by
    have h64 : 64 * (Rbar : ℝ) ≤ (64 * (E + 2)) * s := by nlinarith
    have hlog := Real.log_le_log
      (show (0 : ℝ) < 64 * (Rbar : ℝ) by positivity) h64
    rw [Real.log_mul (by positivity : (64 * (E + 2) : ℝ) ≠ 0) (ne_of_gt hspos)] at hlog
    have hconst : Real.log (64 * (E + 2)) ≤ Real.log s :=
      Real.log_le_log (by positivity : (0 : ℝ) < 64 * (E + 2)) hsgeom
    linarith
  have hcs : 8 * (E + 2) ≤ c * s := by
    have h := (div_le_iff₀ hc).mp hsmove
    nlinarith
  have hsq : s ^ 2 ≤ 4 * (N : ℝ) := by
    have h := ElementaryLogGrowth.square_le_four_mul_exp hs0
    simpa only [s, Real.exp_log hNpos] using h
  have hwindow : 2 * (E + 2) * s ≤ c * N := by
    have hmul := mul_le_mul_of_nonneg_right hcs hs0
    have hsqmul := mul_le_mul_of_nonneg_left hsq hc.le
    nlinarith
  have hUbarReal : (2 : ℝ) * Rbar ≤ (U : ℝ) := by
    calc
      (2 : ℝ) * Rbar ≤ 2 * ((E + 2) * s) :=
        mul_le_mul_of_nonneg_left hbarhi (by norm_num)
      _ = 2 * (E + 2) * s := by ring
      _ ≤ c * N := hwindow
      _ ≤ U := hUlo
  have hUbar : 2 * Rbar ≤ U := by exact_mod_cast hUbarReal
  have htpos : 1 ≤ codingRadius U Rbar :=
    (codingRadius_lower hs hlogUlo hbarlogpos hbarloghi).1
  have hbudget : primeCount H + 1 ≤ A * codingRadius U Rbar :=
    prime_count_radius_budget D hD hs hH hlogUlo hbarlogpos hbarloghi
  have hcard := card_lt_of_count_ratio hbarOne hUbar htpos
    (codingRadius_log_strict (by omega) hbarOne) hbudget
  let q : ℝ := Real.log U / (4 * Real.log (64 * (Rbar : ℝ)))
  have htupper : (codingRadius U Rbar : ℝ) ≤ q :=
    Nat.floor_le (div_nonneg (by linarith : 0 ≤ Real.log (U : ℝ)) (by positivity))
  have hqupper : q ≤ s / Real.log s := by
    dsimp [q]
    apply (div_le_div_iff₀
      (by positivity : 0 < 4 * Real.log (64 * (Rbar : ℝ))) hlogs).mpr
    calc
      Real.log U * Real.log s ≤ (2 * s) * Real.log s :=
        mul_le_mul_of_nonneg_right hlogUhi hlogs.le
      _ ≤ (4 * s) * Real.log s :=
        mul_le_mul_of_nonneg_right (by linarith) hlogs.le
      _ = s * (4 * Real.log s) := by ring
      _ ≤ s * (4 * Real.log (64 * (Rbar : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hs0
  have hcast : ((defectsInInterval H U Rbar).card : ℝ) <
      ((2 * codingRadius U Rbar * 2 ^ (A + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
  have hfinal : ((defectsInInterval H U Rbar).card : ℝ) ≤
      ((2 * 2 ^ (A + 1) : ℕ) : ℝ) * s / Real.log s := by
    apply le_of_lt
    calc
      _ < ((2 * codingRadius U Rbar * 2 ^ (A + 1) : ℕ) : ℝ) := hcast
      _ = ((2 * 2 ^ (A + 1) : ℕ) : ℝ) * (codingRadius U Rbar : ℝ) := by push_cast; ring
      _ ≤ ((2 * 2 ^ (A + 1) : ℕ) : ℝ) * (s / Real.log s) :=
        mul_le_mul_of_nonneg_left (htupper.trans hqupper) (by positivity)
      _ = _ := by ring
  exact (by exact_mod_cast card_mono_width (H := H) (U := U) hRbar :
    ((defectsInInterval H U R).card : ℝ) ≤ ((defectsInInterval H U Rbar).card : ℝ)).trans hfinal

end PaperP1.LocalDefectAsymptotic

