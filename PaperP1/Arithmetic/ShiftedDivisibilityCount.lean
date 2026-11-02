module

public import PaperP1.Diophantine.IntegerLinearFibres

/-! # A height-weighted count for two actual shifted divisibilities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedDivisibilityCount

open Finset

theorem uniform_finite (A B h : ℕ) (hA : 0 < A) (hB : 0 < B) (hh : 0 < h)
    (X : ℝ) (hX : 0 ≤ X) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ X ∧ A ∣ n ∧ B ∣ n + h) :
    (S.card : ℝ) ≤ X * h / ((A : ℝ) * B) + 1 := by
  classical
  let f : ℕ → ℤ × ℤ := fun n ↦ ((n / A : ℕ), ((n + h) / B : ℕ))
  have hfirst (n : ℕ) (hn : n ∈ S) : A * (n / A) = n := Nat.mul_div_cancel' (hS n hn).2.2.1
  have hsecond (n : ℕ) (hn : n ∈ S) : B * ((n + h) / B) = n + h := Nat.mul_div_cancel' (hS n hn).2.2.2
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro n hn m hm hnm
    have heq : n / A = m / A := by
      have hh' := congrArg Prod.fst hnm
      change ((n / A : ℕ) : ℤ) = ((m / A : ℕ) : ℤ) at hh'
      exact_mod_cast hh'
    rw [← hfirst n hn, ← hfirst m hm, heq]
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hcount := IntegerLinearFibres.weighted_height_count A B hA hB (h : ℤ)
    (by exact_mod_cast hh.ne') X (X / ((A : ℝ) * B)) 1 hX (by positivity) (by norm_num)
    (by apply le_of_eq; field_simp) (S.image f) (by
      intro z hz
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
      change (B : ℤ) * ((n + h) / B : ℕ) - (A : ℤ) * (n / A : ℕ) = h
      have h1 : (A : ℤ) * (n / A : ℕ) = n := by exact_mod_cast hfirst n hn
      have h2 : (B : ℤ) * ((n + h) / B : ℕ) = (n : ℤ) + h := by exact_mod_cast hsecond n hn
      rw [h1, h2]
      ring) (by
      intro z hz
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
      have hp : 0 < n / A := Nat.div_pos (Nat.le_of_dvd (hS n hn).1 (hS n hn).2.2.1) hA
      change (0 : ℤ) < ((n / A : ℕ) : ℤ)
      exact_mod_cast hp) (by
      intro z hz
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
      have heq : (A : ℝ) * (n / A : ℕ) = n := by exact_mod_cast hfirst n hn
      simpa only [f, heq, one_mul, Int.cast_natCast] using (hS n hn).2.1)
  rw [card_image_of_injOn hinj] at hcount
  simpa only [mul_one, Int.natAbs_natCast, div_mul_eq_mul_div] using hcount

end PaperP1.ShiftedDivisibilityCount
