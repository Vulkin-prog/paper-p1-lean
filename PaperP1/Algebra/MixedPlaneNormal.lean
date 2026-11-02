module

public import PaperP1.Algebra.TripleCross

/-! # A small-constant integer plane meeting a positive cube has opposite normal signs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MixedPlaneNormal

open Finset PaperP1.TripleCross

theorem nonnegative_dot_lower (N : ℕ) (A X : Fin 3 → ℤ) (hA : A ≠ 0)
    (hcoord : ∀ i, 0 ≤ A i) (hX : ∀ i, (N : ℤ) ≤ X i) : (N : ℤ) ≤ dot A X := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < A i := by
    by_contra hh
    push Not at hh
    apply hA
    funext i
    have ha := hcoord i
    have hb := hh i
    change A i = 0
    omega
  have hXnonneg (j : Fin 3) : 0 ≤ X j := (Int.natCast_nonneg N).trans (hX j)
  have hterm : (N : ℤ) ≤ A i * X i := by
    have hh := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ A i by omega) (hXnonneg i)
    nlinarith only [hh, hX i]
  have hsum' : A i * X i ≤ dot A X := by
    have h0 := mul_nonneg (hcoord 0) (hXnonneg 0)
    have h1 := mul_nonneg (hcoord 1) (hXnonneg 1)
    have h2 := mul_nonneg (hcoord 2) (hXnonneg 2)
    fin_cases i <;> norm_num [dot] at * <;> linarith only [h0, h1, h2]
  exact hterm.trans hsum'

theorem opposite_signs (N : ℕ) (A X : Fin 3 → ℤ) (h : ℤ) (hA : A ≠ 0)
    (hX : ∀ i, (N : ℤ) ≤ X i) (hplane : dot A X = h) (hsmall : h.natAbs < N) :
    ∃ i j : Fin 3, 0 < A i ∧ A j < 0 ∧ i ≠ j := by
  have habs : |h| < (N : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hsmall
  have hpos : ∃ i : Fin 3, 0 < A i := by
    by_contra hh
    push Not at hh
    have hnegA : -A ≠ 0 := neg_ne_zero.mpr hA
    have hcoord : ∀ i, 0 ≤ (-A) i := fun i ↦ by have hi := hh i; change 0 ≤ -A i; omega
    have hlow := nonnegative_dot_lower N (-A) X hnegA hcoord hX
    have he : dot (-A) X = -h := by simp only [dot, Pi.neg_apply]; rw [← hplane]; unfold dot; ring
    rw [he] at hlow
    have hn := neg_le_abs h
    linarith only [hlow, hn, habs]
  have hneg : ∃ j : Fin 3, A j < 0 := by
    by_contra hh
    push Not at hh
    have hlow := nonnegative_dot_lower N A X hA hh hX
    rw [hplane] at hlow
    have hn := le_abs_self h
    linarith only [hlow, hn, habs]
  obtain ⟨i, hi⟩ := hpos
  obtain ⟨j, hj⟩ := hneg
  exact ⟨i, j, hi, hj, by intro heq; rw [heq] at hi; omega⟩

theorem exists_perm_pair (i j : Fin 3) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by
  fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
  all_goals first
    | exact ⟨Equiv.refl _, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 1, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 2, by decide, by decide⟩
    | exact ⟨Equiv.swap 1 2, by decide, by decide⟩
    | exact ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), by decide, by decide⟩
    | exact ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), by decide, by decide⟩

theorem positive_permutation (N : ℕ) (A X : Fin 3 → ℤ) (h : ℤ) (hA : A ≠ 0)
    (hX : ∀ i, (N : ℤ) ≤ X i) (hplane : dot A X = h) (hsmall : h.natAbs < N) :
    ∃ e : Equiv.Perm (Fin 3), 0 < A (e 0) ∧ A (e 1) < 0 := by
  obtain ⟨i, j, hi, hj, hij⟩ := opposite_signs N A X h hA hX hplane hsmall
  obtain ⟨e, he0, he1⟩ := exists_perm_pair i j hij
  exact ⟨e, by rw [he0]; exact hi, by rw [he1]; exact hj⟩

theorem dot_permutation (A X : Fin 3 → ℤ) (e : Equiv.Perm (Fin 3)) :
    dot (A ∘ e) (X ∘ e) = dot A X := by
  have hh := Equiv.sum_comp e (fun i ↦ A i * X i)
  simpa only [Fin.sum_univ_three, dot, Function.comp_apply] using hh

end PaperP1.MixedPlaneNormal
