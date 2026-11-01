module

public import PaperP1.Algebra.TripleCross

/-! # A plane through rigid positive projections uses every coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneNormalRigidity

open PaperP1.TripleCross

def ProjectionRigid (V : Fin 3 → Fin 3 → ℤ) : Prop :=
  ∀ i j : Fin 3, i ≠ j → ∀ p q : Fin 3,
    V p i * V q j = V q i * V p j → V p i = V q i

theorem normal_zero_of_two_constant (V : Fin 3 → Fin 3 → ℤ) (j k : Fin 3) (hjk : j ≠ k)
    (hj : ∀ p, V p j = V 0 j) (hk : ∀ p, V p k = V 0 k) : normal (V 0) (V 1) (V 2) = 0 := by
  funext i
  fin_cases j <;> fin_cases k <;> fin_cases i <;> norm_num at * <;>
    simp [normal, cross, Pi.sub_apply, hj, hk]

theorem two_coordinate_plane_constant (V : Fin 3 → Fin 3 → ℤ) (j k : Fin 3) (hjk : j ≠ k)
    (a b : ℤ) (hab : ¬(a = 0 ∧ b = 0)) (hpos : ∀ p i, 0 < V p i)
    (hplane : ∀ p, a * V p j + b * V p k = 0) (hrigid : ProjectionRigid V) :
    (∀ p, V p j = V 0 j) ∧ ∀ p, V p k = V 0 k := by
  have hb : b ≠ 0 := by
    intro hb
    apply hab
    refine ⟨?_, hb⟩
    have h := hplane 0
    rw [hb, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (hpos 0 j).ne'
  have hcross (p q : Fin 3) : V p j * V q k = V q j * V p k := by
    have helim : b * (V p j * V q k - V q j * V p k) = 0 := by
      calc
        _ = V p j * (a * V q j + b * V q k) - V q j * (a * V p j + b * V p k) := by ring
        _ = 0 := by rw [hplane q, hplane p]; ring
    have hz := (mul_eq_zero.mp helim).resolve_left hb
    exact sub_eq_zero.mp hz
  constructor
  · exact fun p ↦ hrigid j k hjk p 0 (hcross p 0)
  · intro p
    apply hrigid k j hjk.symm p 0
    have h := hcross p 0
    nlinarith

theorem normal_coordinates_ne_zero (V : Fin 3 → Fin 3 → ℤ)
    (hpos : ∀ p i, 0 < V p i) (hrigid : ProjectionRigid V)
    (hA : normal (V 0) (V 1) (V 2) ≠ 0)
    (hplane : ∀ p, dot (normal (V 0) (V 1) (V 2)) (V p) = 0) :
    ∀ i, normal (V 0) (V 1) (V 2) i ≠ 0 := by
  let A := normal (V 0) (V 1) (V 2)
  have hA' : A ≠ 0 := hA
  intro i hi
  change A i = 0 at hi
  fin_cases i
  · norm_num at hi
    have hab : ¬(A 1 = 0 ∧ A 2 = 0) := by
      rintro ⟨h1, h2⟩
      apply hA'
      funext j
      fin_cases j
      · exact hi
      · exact h1
      · exact h2
    have hp (p : Fin 3) : A 1 * V p 1 + A 2 * V p 2 = 0 := by
      have h := hplane p
      change dot A (V p) = 0 at h
      simpa only [dot, hi, zero_mul, zero_add] using h
    obtain ⟨hj, hk⟩ := two_coordinate_plane_constant V 1 2 (by decide) (A 1) (A 2) hab hpos hp hrigid
    exact hA (normal_zero_of_two_constant V 1 2 (by decide) hj hk)
  · norm_num at hi
    have hab : ¬(A 0 = 0 ∧ A 2 = 0) := by
      rintro ⟨h0, h2⟩
      apply hA'
      funext j
      fin_cases j
      · exact h0
      · exact hi
      · exact h2
    have hp (p : Fin 3) : A 0 * V p 0 + A 2 * V p 2 = 0 := by
      have h := hplane p
      change dot A (V p) = 0 at h
      simpa only [dot, hi, zero_mul, add_zero] using h
    obtain ⟨hj, hk⟩ := two_coordinate_plane_constant V 0 2 (by decide) (A 0) (A 2) hab hpos hp hrigid
    exact hA (normal_zero_of_two_constant V 0 2 (by decide) hj hk)
  · norm_num at hi
    have hab : ¬(A 0 = 0 ∧ A 1 = 0) := by
      rintro ⟨h0, h1⟩
      apply hA'
      funext j
      fin_cases j
      · exact h0
      · exact h1
      · exact hi
    have hp (p : Fin 3) : A 0 * V p 0 + A 1 * V p 1 = 0 := by
      have h := hplane p
      change dot A (V p) = 0 at h
      simpa only [dot, hi, zero_mul, add_zero] using h
    obtain ⟨hj, hk⟩ := two_coordinate_plane_constant V 0 1 (by decide) (A 0) (A 1) hab hpos hp hrigid
    exact hA (normal_zero_of_two_constant V 0 1 (by decide) hj hk)

end PaperP1.PlaneNormalRigidity
