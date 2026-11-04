module

public import PaperP1.Analysis.ReducedSourceShiftBudget

/-! # Retain a separate polylogarithmic weakening of the original source barrier -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedReducedSourceBarrier

open PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter PaperP1.ReducedSourceBarrier

theorem transfer (N g q : ℕ) (Γ c₁ c₂ D E : ℝ) (hg : 0 < g) (hq : 0 < q)
    (hΓ : 0 ≤ Γ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hbarrier : (N : ℝ) ≤ Γ * c₁ * c₂ * (D * E) ^ 2) (heff : 1 ≤ effective N (g ^ 2 * q)) :
    (parameter N (g ^ 2 * q) : ℝ) ≤ (Γ * loss g q) * c₁ * c₂ * (enlarged D g * enlarged E g) ^ 2 := by
  have hsR : (0 : ℝ) < ((g ^ 2 * q : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (pow_pos hg 2) hq
  have hd : effective N (g ^ 2 * q) ≤ Γ * ((c₁ * c₂ * (D * E) ^ 2) / ((g ^ 2 * q : ℕ) : ℝ)) := by
    have hh := div_le_div_of_nonneg_right hbarrier hsR.le
    unfold effective
    convert hh using 1
    ring
  have hl := mul_le_mul_of_nonneg_left (source_barrier_lower c₁ c₂ D E g hg hc₁ hc₂ hD hE) (loss_nonnegative g q)
  rw [loss_identity (c₁ * c₂ * (D * E) ^ 2) g q hg hq] at hl
  have hΓl := mul_le_mul_of_nonneg_left hl hΓ
  calc
    _ ≤ 2 * effective N (g ^ 2 * q) := parameter_upper N (g ^ 2 * q) heff
    _ ≤ 2 * (Γ * ((c₁ * c₂ * (D * E) ^ 2) / ((g ^ 2 * q : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = Γ * (2 * ((c₁ * c₂ * (D * E) ^ 2) / ((g ^ 2 * q : ℕ) : ℝ))) := by ring
    _ ≤ Γ * (loss g q * (c₁ * c₂ * (enlarged D g * enlarged E g) ^ 2)) := hΓl
    _ = _ := by ring

theorem product_budget (N g q h : ℕ) (hN : 0 < N) (hg : 0 < g) (hq : 0 < q)
    (hscale : g ^ 2 * q ≤ h) (hroot : (h : ℝ) ≤ Real.sqrt N)
    (Kbar Abar Kshift Ashift Γ : ℝ) (hKbar : 0 ≤ Kbar) (hAbar : 0 ≤ Abar)
    (hKshift : 0 ≤ Kshift) (hAshift : 0 ≤ Ashift) (hΓ : 0 ≤ Γ)
    (hΓbudget : Γ ≤ Kbar * (Real.log N) ^ Abar) (hshift : (h : ℝ) ≤ Kshift * (Real.log N) ^ Ashift) :
    0 ≤ Γ * loss g q ∧ Γ * loss g q ≤
      ((Kbar * (2 : ℝ) ^ Abar) * (2 * Kshift * (2 : ℝ) ^ Ashift)) *
        (Real.log (parameter N (g ^ 2 * q))) ^ (Abar + Ashift) := by
  have hs : 0 < g ^ 2 * q := Nat.mul_pos (pow_pos hg 2) hq
  have hp := parameter_positive N (g ^ 2 * q) hN hs
  have ht : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have ht' : 0 ≤ Real.log (parameter N (g ^ 2 * q)) := Real.log_nonneg (by exact_mod_cast hp)
  have hlog := parameter_log_lower N (g ^ 2 * q) h hN hs hscale hroot
  have hΓ' := ReducedSourceShiftBudget.polylog_rebase Kbar Abar (Real.log N) (Real.log (parameter N (g ^ 2 * q)))
    Γ hKbar hAbar ht ht' (by linarith) hΓbudget
  have hl := (ReducedSourceShiftBudget.shift_and_loss_bounds N g q h hN hg hq hscale hroot
    Kshift Ashift hKshift hAshift hshift).2.2.2
  refine ⟨mul_nonneg hΓ (loss_nonnegative g q), ?_⟩
  calc
    _ ≤ ((Kbar * (2 : ℝ) ^ Abar) * (Real.log (parameter N (g ^ 2 * q))) ^ Abar) *
        ((2 * Kshift * (2 : ℝ) ^ Ashift) * (Real.log (parameter N (g ^ 2 * q))) ^ Ashift) :=
      mul_le_mul hΓ' hl (loss_nonnegative g q) (by positivity)
    _ = _ := by rw [Real.rpow_add_of_nonneg ht' hAbar hAshift]; ring

end PaperP1.WeightedReducedSourceBarrier
