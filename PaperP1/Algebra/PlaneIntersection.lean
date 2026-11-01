module

public import PaperP1.Algebra.TripleCross
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp

/-! # Two distinct integral planes: proportional normals or an injective coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneIntersection

open PaperP1.TripleCross

def realDot (A : Fin 3 → ℤ) (x : Fin 3 → ℝ) : ℝ := (A 0 : ℝ) * x 0 + (A 1 : ℝ) * x 1 + (A 2 : ℝ) * x 2

def plane (A : Fin 3 → ℤ) (h : ℤ) : Set (Fin 3 → ℝ) := {x | realDot A x = (h : ℝ)}

theorem realDot_int_cast (A X : Fin 3 → ℤ) : realDot A (fun i ↦ (X i : ℝ)) = (dot A X : ℝ) := by
  simp only [realDot, dot, Int.cast_add, Int.cast_mul]

theorem exists_nonzero_coordinate (A : Fin 3 → ℤ) (hA : A ≠ 0) : ∃ i, A i ≠ 0 := by
  by_contra hnot
  apply hA
  funext i
  change A i = 0
  by_contra h
  exact hnot ⟨i, h⟩

theorem planes_equal_of_cross_zero_meet (A B X : Fin 3 → ℤ) (h k : ℤ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hcross : cross A B = 0) (hX : dot A X = h) (hY : dot B X = k) :
    plane A h = plane B k := by
  obtain ⟨i, hi⟩ := exists_nonzero_coordinate A hA
  have hminor := (cross_eq_zero_iff_minors A B).mp hcross
  have hBi : B i ≠ 0 := by
    intro hz
    apply hB
    funext j
    have h := hminor i j
    rw [hz, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hi
  have hiR : (A i : ℝ) ≠ 0 := by exact_mod_cast hi
  have hBiR : (B i : ℝ) ≠ 0 := by exact_mod_cast hBi
  let t : ℝ := (B i : ℝ) / (A i : ℝ)
  have ht0 : t ≠ 0 := div_ne_zero hBiR hiR
  have ht (j : Fin 3) : (B j : ℝ) = t * (A j : ℝ) := by
    have hR : (A i : ℝ) * (B j : ℝ) = (A j : ℝ) * (B i : ℝ) := by exact_mod_cast hminor i j
    unfold t
    field_simp
    nlinarith
  have hdot (x : Fin 3 → ℝ) : realDot B x = t * realDot A x := by
    unfold realDot
    rw [ht 0, ht 1, ht 2]
    ring
  have hk : (k : ℝ) = t * (h : ℝ) := by
    calc
      _ = realDot B (fun j ↦ (X j : ℝ)) := by rw [realDot_int_cast, hY]
      _ = t * realDot A (fun j ↦ (X j : ℝ)) := hdot _
      _ = _ := by rw [realDot_int_cast, hX]
  ext x
  change realDot A x = (h : ℝ) ↔ realDot B x = (k : ℝ)
  rw [hdot, hk]
  constructor
  · exact congrArg (fun z : ℝ ↦ t * z)
  · exact mul_left_cancel₀ ht0

theorem cross_ne_zero_of_distinct_meeting (A B X : Fin 3 → ℤ) (h k : ℤ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hne : plane A h ≠ plane B k) (hX : dot A X = h) (hY : dot B X = k) :
    cross A B ≠ 0 := by
  intro hz
  exact hne (planes_equal_of_cross_zero_meet A B X h k hA hB hz hX hY)

theorem two_equations_kernel (a b c d y z : ℤ) (hdet : a * d - b * c ≠ 0)
    (h1 : a * y + b * z = 0) (h2 : c * y + d * z = 0) : y = 0 ∧ z = 0 := by
  have hy : (a * d - b * c) * y = 0 := by
    calc
      _ = d * (a * y + b * z) - b * (c * y + d * z) := by ring
      _ = 0 := by rw [h1, h2]; ring
  have hz : (a * d - b * c) * z = 0 := by
    calc
      _ = a * (c * y + d * z) - c * (a * y + b * z) := by ring
      _ = 0 := by rw [h1, h2]; ring
  exact ⟨(mul_eq_zero.mp hy).resolve_left hdet, (mul_eq_zero.mp hz).resolve_left hdet⟩

theorem kernel_zero_of_coordinate (A B v : Fin 3 → ℤ) (k : Fin 3)
    (hk : cross A B k ≠ 0) (hA : dot A v = 0) (hB : dot B v = 0) (hv : v k = 0) : v = 0 := by
  fin_cases k
  · norm_num [cross] at hk
    norm_num at hv
    have h1 : A 1 * v 1 + A 2 * v 2 = 0 := by simpa only [dot, hv, mul_zero, zero_add] using hA
    have h2 : B 1 * v 1 + B 2 * v 2 = 0 := by simpa only [dot, hv, mul_zero, zero_add] using hB
    obtain ⟨h1, h2⟩ := two_equations_kernel _ _ _ _ _ _ hk h1 h2
    funext i
    fin_cases i
    · exact hv
    · exact h1
    · exact h2
  · norm_num [cross] at hk
    norm_num at hv
    have h1 : A 2 * v 2 + A 0 * v 0 = 0 := by have h := hA; simp only [dot, hv, mul_zero, add_zero] at h; linarith
    have h2 : B 2 * v 2 + B 0 * v 0 = 0 := by have h := hB; simp only [dot, hv, mul_zero, add_zero] at h; linarith
    obtain ⟨h2, h0⟩ := two_equations_kernel _ _ _ _ _ _ hk h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact hv
    · exact h2
  · norm_num [cross] at hk
    norm_num at hv
    have h1 : A 0 * v 0 + A 1 * v 1 = 0 := by simpa only [dot, hv, mul_zero, add_zero] using hA
    have h2 : B 0 * v 0 + B 1 * v 1 = 0 := by simpa only [dot, hv, mul_zero, add_zero] using hB
    obtain ⟨h0, h1⟩ := two_equations_kernel _ _ _ _ _ _ hk h1 h2
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact hv

theorem points_eq_of_coordinate (A B X Y : Fin 3 → ℤ) (h k : ℤ) (i : Fin 3)
    (hi : cross A B i ≠ 0) (hAX : dot A X = h) (hBX : dot B X = k)
    (hAY : dot A Y = h) (hBY : dot B Y = k) (hcoord : X i = Y i) : X = Y := by
  have hv : X - Y = 0 := kernel_zero_of_coordinate A B (X - Y) i hi
    (by rw [dot_sub_right, hAX, hAY, sub_self]) (by rw [dot_sub_right, hBX, hBY, sub_self])
    (by change X i - Y i = 0; omega)
  exact sub_eq_zero.mp hv

end PaperP1.PlaneIntersection
