module

public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Monotone.Basic

/-! # An eventually decreasing natural sequence is eventually constant -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.NatEventuallyConstant

theorem of_succ_le (f : ℕ → ℕ) (N : ℕ) (h : ∀ n : ℕ, N ≤ n → f (n + 1) ≤ f n) :
    ∃ M c : ℕ, N ≤ M ∧ ∀ n : ℕ, M ≤ n → f n = c := by
  classical
  have hex : ∃ c : ℕ, ∃ n : ℕ, N ≤ n ∧ f n = c := ⟨f N, N, le_rfl, rfl⟩
  let c := Nat.find hex
  obtain ⟨M, hNM, hM⟩ := Nat.find_spec hex
  refine ⟨M, c, hNM, fun n hn ↦ ?_⟩
  have hmin : c ≤ f n := Nat.find_min' hex ⟨n, hNM.trans hn, rfl⟩
  have hmax : f n ≤ c := ((antitoneOn_nat_Ici_of_succ_le h) hNM (hNM.trans hn) hn).trans_eq hM
  exact Nat.le_antisymm hmax hmin

end PaperP1.NatEventuallyConstant
