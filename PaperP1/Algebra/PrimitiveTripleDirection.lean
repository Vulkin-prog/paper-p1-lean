module

public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega

/-! # Primitive integral directions and all lattice points on a rational line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveTripleDirection

open Finset

def content (w : Fin 3 → ℤ) : ℕ := Int.gcd (w 0) (Int.gcd (w 1) (w 2) : ℤ)

def Primitive (d : Fin 3 → ℤ) : Prop := ∃ s : Fin 3 → ℤ, ∑ i, s i * d i = 1

def height (d : Fin 3 → ℤ) : ℕ := max (d 0).natAbs (max (d 1).natAbs (d 2).natAbs)

theorem content_dvd (w : Fin 3 → ℤ) (i : Fin 3) : (content w : ℤ) ∣ w i := by
  fin_cases i
  · exact Int.gcd_dvd_left _ _
  · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
  · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)

theorem exists_content_combination (w : Fin 3 → ℤ) : ∃ s : Fin 3 → ℤ, ∑ i, s i * w i = content w := by
  let g : ℤ := Int.gcd (w 1) (w 2)
  refine ⟨![Int.gcdA (w 0) g, Int.gcdB (w 0) g * Int.gcdA (w 1) (w 2),
    Int.gcdB (w 0) g * Int.gcdB (w 1) (w 2)], ?_⟩
  simp [Fin.sum_univ_three]
  have hfirst := Int.gcd_eq_gcd_ab (w 0) g
  have hsecond := Int.gcd_eq_gcd_ab (w 1) (w 2)
  change _ = (Int.gcd (w 0) g : ℤ)
  rw [hfirst]
  change g = _ at hsecond
  rw [hsecond]
  ring

theorem content_pos (w : Fin 3 → ℤ) (hw : w ≠ 0) : 0 < content w := by
  by_contra h
  have hg : content w = 0 := by omega
  apply hw
  funext i
  have hi := content_dvd w i
  rw [hg, Nat.cast_zero, zero_dvd_iff] at hi
  exact hi

theorem exists_primitive_direction (w : Fin 3 → ℤ) (hw : w ≠ 0) :
    ∃ g : ℕ, 0 < g ∧ ∃ d : Fin 3 → ℤ, Primitive d ∧ ∀ i, w i = (g : ℤ) * d i := by
  let g := content w
  let d : Fin 3 → ℤ := fun i ↦ w i / (g : ℤ)
  have hg : 0 < g := content_pos w hw
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hfactor (i : Fin 3) : w i = (g : ℤ) * d i := by
    dsimp [d]
    rw [mul_comm]
    exact (Int.ediv_mul_cancel (content_dvd w i)).symm
  obtain ⟨s, hs⟩ := exists_content_combination w
  have hprimitive : Primitive d := by
    refine ⟨s, ?_⟩
    apply mul_left_cancel₀ hg0
    rw [mul_one, mul_sum]
    calc
      _ = ∑ i, s i * w i := sum_congr rfl (fun i _ ↦ by rw [hfactor i]; ring)
      _ = _ := hs
  exact ⟨g, hg, d, hprimitive, hfactor⟩

theorem primitive_ne_zero (d : Fin 3 → ℤ) (hd : Primitive d) : d ≠ 0 := by
  obtain ⟨s, hs⟩ := hd
  intro h
  rw [h] at hs
  simp only [Pi.zero_apply, mul_zero, sum_const_zero] at hs
  omega

theorem primitive_iff_content_one (d : Fin 3 → ℤ) : Primitive d ↔ content d = 1 := by
  constructor
  · rintro ⟨s, hs⟩
    have hdiv : (content d : ℤ) ∣ 1 := by
      rw [← hs]
      exact dvd_sum (fun i _ ↦ dvd_mul_of_dvd_right (content_dvd d i) (s i))
    have hNat : content d ∣ 1 := by exact_mod_cast hdiv
    exact Nat.dvd_one.mp hNat
  · intro h
    obtain ⟨s, hs⟩ := exists_content_combination d
    exact ⟨s, by simpa only [h, Nat.cast_one] using hs⟩

theorem integer_multiple_of_minors (d v : Fin 3 → ℤ) (hd : Primitive d)
    (hcross : ∀ i j, d i * v j = d j * v i) : ∃ t : ℤ, ∀ i, v i = t * d i := by
  obtain ⟨s, hs⟩ := hd
  refine ⟨∑ j, s j * v j, ?_⟩
  intro i
  calc
    _ = (∑ j, s j * d j) * v i := by rw [hs, one_mul]
    _ = ∑ j, s j * (d j * v i) := by rw [sum_mul]; apply sum_congr rfl; intro j _; ring
    _ = ∑ j, s j * (d i * v j) := sum_congr rfl (fun j _ ↦ by rw [hcross j i])
    _ = _ := by rw [sum_mul]; apply sum_congr rfl; intro j _; ring

theorem coordinate_natAbs_le_height (d : Fin 3 → ℤ) (i : Fin 3) : (d i).natAbs ≤ height d := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem height_pos (d : Fin 3 → ℤ) (hd : Primitive d) : 0 < height d := by
  by_contra h
  have hz : height d = 0 := by omega
  apply primitive_ne_zero d hd
  funext i
  have hi := coordinate_natAbs_le_height d i
  rw [hz] at hi
  exact Int.natAbs_eq_zero.mp (by omega)

theorem height_le_of_factor (w d : Fin 3 → ℤ) (g B : ℕ) (hg : 0 < g)
    (hfactor : ∀ i, w i = (g : ℤ) * d i) (hB : ∀ i, (w i).natAbs ≤ B) : height d ≤ B := by
  have hi (i : Fin 3) : (d i).natAbs ≤ B := by
    have heq : (w i).natAbs = g * (d i).natAbs := by rw [hfactor i, Int.natAbs_mul, Int.natAbs_natCast]
    have hg1 : 1 ≤ g := by omega
    have hle : (d i).natAbs ≤ g * (d i).natAbs := by
      simpa only [one_mul] using Nat.mul_le_mul_right (d i).natAbs hg1
    exact hle.trans (heq ▸ hB i)
  exact max_le (hi 0) (max_le (hi 1) (hi 2))

end PaperP1.PrimitiveTripleDirection
