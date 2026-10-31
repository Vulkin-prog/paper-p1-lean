module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

/-! # The exact ceiling bound for separated integers in a finite interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeparatedPacking

open Finset

theorem ceil_ratio_eq {N L : ℕ} (hN : 0 < N) (hL : 0 < L) :
    ⌈(N : ℝ) / L⌉₊ = (N - 1) / L + 1 := by
  let q := (N - 1) / L
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hlower : q * L < N := (Nat.div_mul_le_self (N - 1) L).trans_lt (by omega)
  have hupper : N ≤ L * (q + 1) := by
    have h := Nat.lt_mul_div_succ (N - 1) hL
    dsimp [q]
    omega
  apply (Nat.ceil_eq_iff (Nat.succ_ne_zero q)).mpr
  constructor
  · apply (lt_div_iff₀ hLreal).mpr
    exact_mod_cast hlower
  · apply (div_le_iff₀ hLreal).mpr
    have h : (N : ℝ) ≤ (L : ℝ) * (q + 1 : ℕ) := by exact_mod_cast hupper
    nlinarith

theorem card_separated_interval {U N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    (A : Finset ℕ) (hA : A ⊆ Ico U (U + N))
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x < y → x + L ≤ y) :
    A.card ≤ ⌈(N : ℝ) / L⌉₊ := by
  let f : ℕ → ℕ := fun x ↦ (x - U) / L
  have hinj : Set.InjOn f (A : Set ℕ) := by
    intro x hx y hy heq
    have hxrange := mem_Ico.mp (hA hx)
    have hyrange := mem_Ico.mp (hA hy)
    have hxdiv := Nat.mod_add_div (x - U) L
    have hydiv := Nat.mod_add_div (y - U) L
    have hxmod := Nat.mod_lt (x - U) hL
    have hymod := Nat.mod_lt (y - U) hL
    change (x - U) / L = (y - U) / L at heq
    rw [heq] at hxdiv
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · have hgap := hsep x hx y hy hxy
      omega
    · have hgap := hsep y hy x hx hyx
      omega
  have hsub : A.image f ⊆ range ((N - 1) / L + 1) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hq
    have hxrange := mem_Ico.mp (hA hx)
    have hdelta : x - U ≤ N - 1 := by omega
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hdelta))
  calc
    A.card = (A.image f).card := (card_image_of_injOn hinj).symm
    _ ≤ (range ((N - 1) / L + 1)).card := card_le_card hsub
    _ = _ := by rw [card_range, ceil_ratio_eq hN hL]

end PaperP1.SeparatedPacking
