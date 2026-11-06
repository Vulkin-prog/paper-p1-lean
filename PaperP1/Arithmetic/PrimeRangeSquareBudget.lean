module

public import PaperP1.Arithmetic.SharpPrimeCount

/-! # Prime-band cardinality and reciprocal-coefficient square budgets from the internal PNT -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeRangeSquareBudget
open Finset PaperP1 PaperP1.LocalDefectBound PaperP1.DefectCounting
open scoped Classical

theorem prime_card_eventually :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ 2*Y) →
      (P.card : ℝ) ≤ 4*Y / Real.log Y := by
  obtain ⟨Y₀, hY₀, hcount⟩ := SharpPrimeCount.primeCount_upper_eventually 1 (by norm_num)
  refine ⟨Y₀, hY₀, ?_⟩
  intro Y hY P hP hupper
  have hYtwo : 2 ≤ Y := hY₀.trans hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hmono : Real.log Y ≤ Real.log ((2*Y : ℕ) : ℝ) :=
    Real.log_le_log hYpos (by exact_mod_cast (show Y ≤ 2*Y by omega))
  have hsub : P ⊆ smallPrimesUpTo (2*Y) := fun p hp ↦
    mem_smallPrimesUpTo.mpr ⟨hP p hp, hupper p hp⟩
  have hcard : (P.card : ℝ) ≤ primeCount (2*Y) := by
    exact_mod_cast (card_le_card hsub)
  have hc := hcount (2*Y) (by omega)
  have hc' : (primeCount (2*Y) : ℝ) ≤ 4*Y / Real.log ((2*Y : ℕ) : ℝ) := by
    convert hc using 1
    norm_num
    ring
  exact hcard.trans (hc'.trans (div_le_div_of_nonneg_left (by positivity) hlog hmono))

theorem reciprocal_square_budget (Y : ℕ) (hY : 1 < Y) (P : Finset ℕ)
    (hlower : ∀ p ∈ P, Y ≤ p)
    (hcard : (P.card : ℝ) ≤ 4*Y / Real.log Y)
    (a : ℕ → ℂ) (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) :
    (∑ p ∈ P, ‖a p / (p : ℂ)‖^2) ≤ 4 / ((Y : ℝ)*Real.log Y) := by
  have hYr : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hlog : 0 < Real.log Y := Real.log_pos (by exact_mod_cast hY)
  have hterm : ∀ p ∈ P, ‖a p / (p : ℂ)‖^2 ≤ 1/(Y : ℝ)^2 := by
    intro p hp
    have hpY : (Y : ℝ) ≤ p := by exact_mod_cast hlower p hp
    have hpr : (0 : ℝ) < p := hYr.trans_le hpY
    have hnorm : ‖a p / (p : ℂ)‖ ≤ 1/(Y : ℝ) := by
      rw [norm_div, Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (ha p hp) hpr.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hYr hpY)
    calc
      _ ≤ (1/(Y : ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm _
      _ = _ := by ring
  calc
    _ ≤ ∑ _p ∈ P, 1/(Y : ℝ)^2 := sum_le_sum hterm
    _ = (P.card : ℝ) / (Y : ℝ)^2 := by simp [div_eq_mul_inv]
    _ ≤ (4*Y / Real.log Y) / (Y : ℝ)^2 := div_le_div_of_nonneg_right hcard (sq_nonneg _)
    _ = _ := by field_simp

theorem reciprocal_square_budget_eventually :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, Y ≤ p ∧ p ≤ 2*Y) →
      ∀ a : ℕ → ℂ, (∀ p ∈ P, ‖a p‖ ≤ 1) →
      (∑ p ∈ P, ‖a p / (p : ℂ)‖^2) ≤ 4 / ((Y : ℝ)*Real.log Y) := by
  obtain ⟨Y₀,hY₀,hcount⟩ := prime_card_eventually
  refine ⟨Y₀,hY₀,?_⟩
  intro Y hY P hP hband a ha
  exact reciprocal_square_budget Y (by omega) P (fun p hp ↦ (hband p hp).1)
    (hcount Y hY P hP (fun p hp ↦ (hband p hp).2)) a ha
end PrimeRangeSquareBudget
