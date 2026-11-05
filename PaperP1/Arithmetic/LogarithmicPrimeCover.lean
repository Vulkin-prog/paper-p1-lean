module

public import PaperP1.Arithmetic.PolynomialPrimeCover

/-! # Actual prime covers with a logarithmic cardinality condition

The PNT interval count retains its full P/log P size. The stronger square-root
restriction m^2 <= P is unnecessary for the finite obstruction-avoidance cover.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LogarithmicPrimeCover

open Finset PaperP1.PolynomialPrimeCover

theorem uniform_pool : ∃ P₀ : ℕ, 16 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ m : ℕ,
    (m : ℝ) * Real.log P ≤ 2 * P →
    ∃ T : Finset ℕ, T.card = m ∧ (∀ p ∈ T, p.Prime ∧ P < p ∧ p ≤ 16 * P) ∧
      (∑ p ∈ T, p) ≤ 16 * m * P ∧
      ∀ n : ℤ, n ≠ 0 → n.natAbs < P ^ m → ∃ p ∈ T, ¬(p : ℤ) ∣ n := by
  classical
  obtain ⟨P₀, hP₀, hcount⟩ := interval_count_lower
  refine ⟨P₀, hP₀, ?_⟩
  intro P hP m hm
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hcardR : (m : ℝ) ≤ (interval P).card :=
    ((le_div_iff₀ hlog).mpr hm).trans (hcount P hP)
  have hcard : m ≤ (interval P).card := by exact_mod_cast hcardR
  obtain ⟨T, hT, hcardT⟩ := exists_subset_card_eq hcard
  have hprime (p : ℕ) (hp : p ∈ T) : p.Prime ∧ P < p ∧ p ≤ 16 * P :=
    (mem_interval P p).mp (hT hp)
  refine ⟨T, hcardT, hprime, ?_, ?_⟩
  · calc
      (∑ p ∈ T, p) ≤ ∑ _p ∈ T, 16 * P := sum_le_sum (fun p hp ↦ (hprime p hp).2.2)
      _ = _ := by simp only [sum_const, smul_eq_mul, hcardT]; ring
  · intro n hn hsmall
    have hprod : P ^ m ≤ ∏ p ∈ T, p := by
      calc
        P ^ m = ∏ _p ∈ T, P := by simp only [prod_const, hcardT]
        _ ≤ _ := prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _) (fun p hp ↦ (hprime p hp).2.1.le)
    exact DyadicPrimeCover.exists_nondividing T (fun p hp ↦ (hprime p hp).1) n hn (hsmall.trans_le hprod)

end PaperP1.LogarithmicPrimeCover
