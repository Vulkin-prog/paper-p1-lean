module

public import PaperP1.Algebra.IntegralLine

/-! # Exact three-coordinate minors and translated determinant identities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleCross

open PaperP1.IntegralLine PaperP1.PrimitiveTripleDirection

def dot (a b : Fin 3 → ℤ) : ℤ := a 0 * b 0 + a 1 * b 1 + a 2 * b 2

def cross (a b : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def determinant (a b c : Fin 3 → ℤ) : ℤ := dot a (cross b c)

def normal (a b c : Fin 3 → ℤ) : Fin 3 → ℤ := cross (b - a) (c - a)

theorem dot_comm (a b : Fin 3 → ℤ) : dot a b = dot b a := by unfold dot; ring

theorem dot_add_right (a b c : Fin 3 → ℤ) : dot a (b + c) = dot a b + dot a c := by
  simp only [dot, Pi.add_apply]
  ring

theorem dot_sub_right (a b c : Fin 3 → ℤ) : dot a (b - c) = dot a b - dot a c := by
  simp only [dot, Pi.sub_apply]
  ring

theorem normal_translate (X a b c : Fin 3 → ℤ) : normal (X + a) (X + b) (X + c) = normal a b c := by
  have h1 : (X + b) - (X + a) = b - a := by funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have h2 : (X + c) - (X + a) = c - a := by funext i; simp only [Pi.add_apply, Pi.sub_apply]; ring
  unfold normal
  rw [h1, h2]

theorem dot_cross_left (a b : Fin 3 → ℤ) : dot a (cross a b) = 0 := by simp [dot, cross]; ring

theorem dot_cross_right (a b : Fin 3 → ℤ) : dot b (cross a b) = 0 := by simp [dot, cross]; ring

theorem determinant_cyclic (a b c : Fin 3 → ℤ) : determinant a b c = determinant b c a := by
  simp [determinant, dot, cross]
  ring

theorem translated_determinant (X a b c : Fin 3 → ℤ) :
    determinant (X + a) (X + b) (X + c) = dot (X + a) (normal a b c) := by
  simp [determinant, dot, normal, cross, Pi.add_apply, Pi.sub_apply]
  ring

theorem determinant_eq_dot_normal (a b c : Fin 3 → ℤ) : determinant a b c = dot a (normal a b c) := by
  simpa only [zero_add] using translated_determinant (0 : Fin 3 → ℤ) a b c

theorem normal_dot_first_difference (a b c : Fin 3 → ℤ) : dot (normal a b c) (b - a) = 0 := by
  rw [normal, dot_comm]
  exact dot_cross_left _ _

theorem normal_dot_second_difference (a b c : Fin 3 → ℤ) : dot (normal a b c) (c - a) = 0 := by
  rw [normal, dot_comm]
  exact dot_cross_right _ _

theorem plane_through_three (V : Fin 3 → Fin 3 → ℤ) (hdet : determinant (V 0) (V 1) (V 2) = 0) :
    ∀ p, dot (normal (V 0) (V 1) (V 2)) (V p) = 0 := by
  have h0 : dot (normal (V 0) (V 1) (V 2)) (V 0) = 0 := by
    rw [dot_comm, ← determinant_eq_dot_normal]
    exact hdet
  have h1 := normal_dot_first_difference (V 0) (V 1) (V 2)
  have h2 := normal_dot_second_difference (V 0) (V 1) (V 2)
  rw [dot_sub_right, h0, sub_zero] at h1 h2
  intro p
  fin_cases p
  · exact h0
  · exact h1
  · exact h2

theorem cross_eq_zero_iff_minors (a b : Fin 3 → ℤ) :
    cross a b = 0 ↔ ∀ i j, a i * b j = a j * b i := by
  constructor
  · intro h i j
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [cross] at h0 h1 h2
    fin_cases i <;> fin_cases j <;> norm_num at * <;> nlinarith
  · intro h
    funext i
    fin_cases i <;> simp [cross, h]

theorem normal_eq_zero_iff_onLine (a b c : Fin 3 → ℤ) : normal a b c = 0 ↔ OnLine a b c :=
  cross_eq_zero_iff_minors (b - a) (c - a)

theorem triple_collinear_of_onLine (a b c : Fin 3 → ℤ) (h : OnLine a b c) :
    Collinear (fun p : Fin 3 ↦ (![a, b, c] p)) := by
  intro p q r i j
  have hij := h i j
  change (b i - a i) * (c j - a j) = (b j - a j) * (c i - a i) at hij
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp <;> nlinarith

theorem collinear_of_normal_zero (u : Fin 3 → Fin 3 → ℤ) (h : normal (u 0) (u 1) (u 2) = 0) :
    Collinear u := by
  have hcol := triple_collinear_of_onLine (u 0) (u 1) (u 2) ((normal_eq_zero_iff_onLine _ _ _).mp h)
  have heta : (fun p : Fin 3 ↦ ![u 0, u 1, u 2] p) = u := by
    funext p
    fin_cases p <;> simp
  rwa [heta] at hcol

theorem pair_collinear (u : Fin 2 → Fin 3 → ℤ) : Collinear u := by
  intro p q r i j
  fin_cases p <;> fin_cases q <;> fin_cases r <;> simp <;> ring

theorem dot_dvd_of_coordinates (p : ℤ) (a b : Fin 3 → ℤ) (h : ∀ i, p ∣ a i) : p ∣ dot a b :=
  ((dvd_mul_of_dvd_left (h 0) (b 0)).add (dvd_mul_of_dvd_left (h 1) (b 1))).add
    (dvd_mul_of_dvd_left (h 2) (b 2))

theorem dot_natAbs_le (a b : Fin 3 → ℤ) (A B : ℕ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B) : (dot a b).natAbs ≤ 3 * A * B := by
  calc
    _ ≤ (a 0 * b 0 + a 1 * b 1).natAbs + (a 2 * b 2).natAbs := Int.natAbs_add_le _ _
    _ ≤ (a 0 * b 0).natAbs + (a 1 * b 1).natAbs + (a 2 * b 2).natAbs :=
      Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = (a 0).natAbs * (b 0).natAbs + (a 1).natAbs * (b 1).natAbs + (a 2).natAbs * (b 2).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ A * B + A * B + A * B := Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul (ha 0) (hb 0)) (Nat.mul_le_mul (ha 1) (hb 1)))
      (Nat.mul_le_mul (ha 2) (hb 2))
    _ = _ := by ring

theorem cross_coordinate_natAbs_le (a b : Fin 3 → ℤ) (A B : ℕ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B) (i : Fin 3) :
    (cross a b i).natAbs ≤ 2 * A * B := by
  have hpair (j k : Fin 3) : (a j * b k - a k * b j).natAbs ≤ 2 * A * B := by
    calc
      _ ≤ (a j * b k).natAbs + (a k * b j).natAbs := Int.natAbs_sub_le _ _
      _ = (a j).natAbs * (b k).natAbs + (a k).natAbs * (b j).natAbs := by rw [Int.natAbs_mul, Int.natAbs_mul]
      _ ≤ A * B + A * B := Nat.add_le_add (Nat.mul_le_mul (ha j) (hb k)) (Nat.mul_le_mul (ha k) (hb j))
      _ = _ := by ring
  fin_cases i
  · simpa [cross] using hpair 1 2
  · simpa [cross] using hpair 2 0
  · simpa [cross] using hpair 0 1

end PaperP1.TripleCross
