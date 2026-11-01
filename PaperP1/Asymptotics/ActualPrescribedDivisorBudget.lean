module

public import PaperP1.Arithmetic.GroupedPrescribedDivisors
public import PaperP1.Asymptotics.GrowingDegreePrimeBudget
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The source enumeration cost for divisors of the actual prescribed e' -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualPrescribedDivisorBudget

open Finset PaperP1.SplitOffsetProducts PaperP1.SquarefreeOutsideDivisor

theorem actual_outside_height (A : Finset ℤ) (N n W e : ℕ) (hWn : W < n)
    (hn : n ≤ 2 * N) (hWN : W ≤ N) (hA : ∀ a ∈ A, a.natAbs ≤ W)
    (he : e ∣ kernel A n) : outside e (resultant A) ≤ (3 * N) ^ A.card := by
  have hd : outside e (resultant A) ∣ kernel A n := (outside_dvd e (resultant A)).trans he
  calc
    _ ≤ kernel A n := Nat.le_of_dvd (kernel_pos A n) hd
    _ ≤ product A n := kernel_le A n (product_pos A n W hWn hA)
    _ ≤ _ := product_le_pow A N n W hn hWN hA

theorem actual_outside_divisor_count (c D A₀ ε : ℝ) (hc : 0 ≤ c)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W e : ℕ, ∀ A : Finset ℤ,
      N ≤ n → n ≤ 2 * N → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      e ∣ kernel A n → ((outside e (resultant A)).divisors.card : ℝ) ≤
        (N : ℝ) ^ (c * Real.log 2 + ε) := by
  obtain ⟨Np, hNp⟩ := PaperP1.GrowingDegreePrimeBudget.squarefree_divisor_budget
    c 3 ε hc (by norm_num) hε
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D) A₀ 1 (by norm_num)
  refine ⟨max 2 (max Np Nw), ?_⟩
  intro N hN n W e A hnlo hnhi hwidth hdegree hA he
  have hWNr : (2 * W : ℝ) ≤ N := by
    have hb := hNw N (by omega)
    rw [Real.rpow_one] at hb
    nlinarith
  have hWN : 2 * W ≤ N := by exact_mod_cast hWNr
  apply hNp N (by omega) (outside e (resultant A)) A.card
    (outside_squarefree e (resultant A)) hdegree
  exact_mod_cast actual_outside_height A N n W e (by omega) hnhi (by omega) hA he

end PaperP1.ActualPrescribedDivisorBudget
