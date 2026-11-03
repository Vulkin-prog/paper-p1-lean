module

public import PaperP1.Arithmetic.TernaryPrimeGroups
public import PaperP1.Arithmetic.FiniteEvenSetRigidity
public import PaperP1.Algebra.TripleCross

/-! # Actual ternary group products divide small arithmetic determinants -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryGroupDeterminants

open Finset PaperP1.Arithmetic PaperP1.TernaryPrimeGroups PaperP1.FiniteEvenSquareClasses
  PaperP1.FiniteEvenSetRigidity PaperP1.TripleCross

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def vector (u : Fin 3 → ℕ) : Fin 3 → ℤ := fun i ↦ (u i : ℤ)

def minor (u v : Fin 3 → ℕ) (i j : Fin 3) : ℤ := (u i : ℤ) * v j - (v i : ℤ) * u j

theorem group_product_dvd_minor (H : ℕ) (u v : Fin 3 → ℕ) (i j : Fin 3) :
    group H u * group H v ∣ (minor u v i j).natAbs := by
  have h1 : (group H u : ℤ) * (group H v : ℤ) ∣ (u i : ℤ) * v j := mul_dvd_mul
    (Int.natCast_dvd_natCast.mpr (group_dvd_value H u i))
    (Int.natCast_dvd_natCast.mpr (group_dvd_value H v j))
  have h2 : (group H u : ℤ) * (group H v : ℤ) ∣ (v i : ℤ) * u j := by
    rw [mul_comm (v i : ℤ) (u j : ℤ)]
    exact mul_dvd_mul (Int.natCast_dvd_natCast.mpr (group_dvd_value H u j))
      (Int.natCast_dvd_natCast.mpr (group_dvd_value H v i))
  apply Int.natCast_dvd.mp
  simpa only [Nat.cast_mul, minor] using dvd_sub h1 h2

theorem minor_bound (u v : Fin 3 → ℕ) (A H : ℕ) (hu : ∀ i, u i ≤ A)
    (hwidth : ∀ i, ((v i : ℤ) - u i).natAbs ≤ H) (i j : Fin 3) :
    (minor u v i j).natAbs ≤ 2 * A * H := by
  have heq : minor u v i j = (u i : ℤ) * ((v j : ℤ) - u j) - (u j : ℤ) * ((v i : ℤ) - u i) := by
    unfold minor
    ring
  rw [heq]
  calc
    _ ≤ ((u i : ℤ) * ((v j : ℤ) - u j)).natAbs + ((u j : ℤ) * ((v i : ℤ) - u i)).natAbs :=
      Int.natAbs_sub_le _ _
    _ = u i * ((v j : ℤ) - u j).natAbs + u j * ((v i : ℤ) - u i).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    _ ≤ A * H + A * H := Nat.add_le_add (Nat.mul_le_mul (hu i) (hwidth j)) (Nat.mul_le_mul (hu j) (hwidth i))
    _ = _ := by ring

theorem group_product_le {U : Fin 3 → Finset ℕ} {A H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    {u v : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (huv : u ≠ v) :
    group H u * group H v ≤ 2 * A * (H + 1) := by
  have hum := (mem_supportPool U u).mp hu
  have hvm := (mem_supportPool U v).mp hv
  by_cases hshared : ∃ i, u i = v i
  · obtain ⟨i, hi⟩ := hshared
    have hcop := group_coprime hwidth hu hv huv
    have hdiv : group H u * group H v ∣ u i := hcop.mul_dvd_of_dvd_of_dvd
      (group_dvd_value H u i) (by rw [hi]; exact group_dvd_value H v i)
    have hle := Nat.le_of_dvd (hpos i (u i) (hum i)) hdiv
    have hm := hmax i (u i) (hum i)
    nlinarith only [hle, hm, Nat.zero_le (A * H)]
  · have hne : minor u v 0 1 ≠ 0 := by
      intro hz
      have hc : u 0 * v 1 = v 0 * u 1 := by exact_mod_cast sub_eq_zero.mp hz
      have heq := projection_equal (hinj 0) (hdirect (by decide : (0 : Fin 3) ≠ 1))
        (hum 0) (hvm 0) (hum 1) (hvm 1) (hpos 0 _ (hum 0)) (hpos 0 _ (hvm 0))
        (hpos 1 _ (hum 1)) (hpos 1 _ (hvm 1)) hc
      exact hshared ⟨0, heq⟩
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (group_product_dvd_minor H u v 0 1)
    have hb := minor_bound u v A H (fun i ↦ hmax i (u i) (hum i))
      (fun i ↦ hwidth i (v i) (hvm i) (u i) (hum i)) 0 1
    exact (hle.trans hb).trans (Nat.mul_le_mul_left (2 * A) (Nat.le_succ H))

theorem determinant_divisible (u v w : Fin 3 → ℤ) (p q r : ℤ)
    (hu : ∀ i, p ∣ u i) (hv : ∀ i, q ∣ v i) (hw : ∀ i, r ∣ w i) :
    p * q * r ∣ determinant u v w := by
  let a : Fin 3 → ℤ := fun i ↦ Classical.choose (hu i)
  let b : Fin 3 → ℤ := fun i ↦ Classical.choose (hv i)
  let c : Fin 3 → ℤ := fun i ↦ Classical.choose (hw i)
  have ha (i : Fin 3) : u i = p * a i := Classical.choose_spec (hu i)
  have hb (i : Fin 3) : v i = q * b i := Classical.choose_spec (hv i)
  have hc (i : Fin 3) : w i = r * c i := Classical.choose_spec (hw i)
  refine ⟨determinant a b c, ?_⟩
  simp [determinant, dot, cross, ha, hb, hc]
  ring

theorem group_triple_dvd_determinant (H : ℕ) (u v w : Fin 3 → ℕ) :
    group H u * group H v * group H w ∣ (determinant (vector u) (vector v) (vector w)).natAbs := by
  apply Int.natCast_dvd.mp
  have h := determinant_divisible (vector u) (vector v) (vector w) (group H u) (group H v) (group H w)
    (fun i ↦ Int.natCast_dvd_natCast.mpr (group_dvd_value H u i))
    (fun i ↦ Int.natCast_dvd_natCast.mpr (group_dvd_value H v i))
    (fun i ↦ Int.natCast_dvd_natCast.mpr (group_dvd_value H w i))
  simpa only [Nat.cast_mul] using h

theorem determinant_bound (u v w : Fin 3 → ℕ) (A H : ℕ) (hu : ∀ i, u i ≤ A)
    (hv : ∀ i, ((v i : ℤ) - u i).natAbs ≤ H)
    (hw : ∀ i, ((w i : ℤ) - u i).natAbs ≤ H) :
    (determinant (vector u) (vector v) (vector w)).natAbs ≤ 6 * A * H ^ 2 := by
  have hnormal (i : Fin 3) : (normal (vector u) (vector v) (vector w) i).natAbs ≤ 2 * H ^ 2 := by
    have h := cross_coordinate_natAbs_le (vector v - vector u) (vector w - vector u) H H hv hw i
    simpa only [normal, pow_two, mul_assoc] using h
  rw [determinant_eq_dot_normal]
  have huabs (i : Fin 3) : (vector u i).natAbs ≤ A := by simpa only [vector, Int.natAbs_natCast] using hu i
  have h := dot_natAbs_le (vector u) (normal (vector u) (vector v) (vector w)) A (2 * H ^ 2) huabs hnormal
  nlinarith only [h]

theorem determinant_zero_of_large_groups {U : Fin 3 → Finset ℕ} {A H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hmax : ∀ i, ∀ n ∈ U i, n ≤ A) {u v w : Fin 3 → ℕ}
    (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (hw : w ∈ supportPool U)
    (hlarge : 6 * A * H ^ 2 < group H u * group H v * group H w) :
    determinant (vector u) (vector v) (vector w) = 0 := by
  by_contra hne
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (group_triple_dvd_determinant H u v w)
  have hum := (mem_supportPool U u).mp hu
  have hvm := (mem_supportPool U v).mp hv
  have hwm := (mem_supportPool U w).mp hw
  have hb := determinant_bound u v w A H (fun i ↦ hmax i (u i) (hum i))
    (fun i ↦ hwidth i (v i) (hvm i) (u i) (hum i))
    (fun i ↦ hwidth i (w i) (hwm i) (u i) (hum i))
  omega

end PaperP1.TernaryGroupDeterminants
