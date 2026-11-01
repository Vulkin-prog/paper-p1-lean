module

public import PaperP1.Arithmetic.ThreeWindowRigidity
public import PaperP1.Arithmetic.IndexedPrimeOffsets

/-! # The actual offset-plane coefficients, heights and further-prime threshold -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetPlaneGeometry

open Finset PaperP1.TripleCross PaperP1.ThreeWindowRigidity PaperP1.OffsetLinePopulation
  PaperP1.PlaneNormalRigidity PaperP1.SaturationPrimes PaperP1.Arithmetic

abbrev Code (L : ℕ) := Fin 3 → Fin 3 → Fin (L + 1)

def planeNormal {L : ℕ} (u : Code L) : Fin 3 → ℤ :=
  normal (offsetVector (u 0)) (offsetVector (u 1)) (offsetVector (u 2))

def planeConstant {L : ℕ} (u : Code L) : ℤ := -dot (planeNormal u) (offsetVector (u 0))

def Contains {L : ℕ} (u : Code L) (X : Fin 3 → ℕ) : Prop := dot (planeNormal u) (fun i ↦ (X i : ℤ)) = planeConstant u

theorem card_codes (L : ℕ) : Fintype.card (Code L) = (L + 1) ^ 9 := by
  simp only [Code, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul]

theorem normal_coordinate_bound {L : ℕ} (u : Code L) (i : Fin 3) :
    (planeNormal u i).natAbs ≤ 2 * (L + 1) ^ 2 := by
  have h := cross_coordinate_natAbs_le
    (offsetVector (u 1) - offsetVector (u 0)) (offsetVector (u 2) - offsetVector (u 0))
    (L + 1) (L + 1) (offset_difference_natAbs_le (u 1) (u 0))
      (offset_difference_natAbs_le (u 2) (u 0)) i
  simpa only [planeNormal, normal, pow_two, mul_assoc] using h

theorem constant_bound {L : ℕ} (u : Code L) : (planeConstant u).natAbs ≤ 6 * (L + 1) ^ 3 := by
  have h := dot_natAbs_le (planeNormal u) (offsetVector (u 0)) (2 * (L + 1) ^ 2) (L + 1)
    (normal_coordinate_bound u) (offset_natAbs_le (u 0))
  rw [planeConstant, Int.natAbs_neg]
  nlinarith [h]

theorem normal_valueVector_eq {L : ℕ} (X : Fin 3 → ℕ) (u : Code L) :
    normal (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2)) = planeNormal u := by
  exact normal_translate (fun i ↦ (X i : ℤ)) (offsetVector (u 0)) (offsetVector (u 1)) (offsetVector (u 2))

theorem value_natAbs_le {L N : ℕ} (X : Fin 3 → ℕ) (v : Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N)) (i : Fin 3) :
    (valueVector X v i).natAbs ≤ 3 * N := by
  have hx : 0 < X i := by have h := (mem_Ico.mp (hX i)).1; omega
  rw [valueVector_eq_natural X v i hx, Int.natAbs_natCast]
  exact (value_bounds hN hLN (hX i) (v i)).2

theorem determinant_bound {L N : ℕ} (X : Fin 3 → ℕ) (u : Code L)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N)) :
    (determinant (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2))).natAbs ≤
      18 * N * (L + 1) ^ 2 := by
  rw [determinant_eq_dot_normal, normal_valueVector_eq]
  have h := dot_natAbs_le (valueVector X (u 0)) (planeNormal u) (3 * N) (2 * (L + 1) ^ 2)
    (value_natAbs_le X (u 0) hN hLN hX) (normal_coordinate_bound u)
  nlinarith [h]

theorem contains_of_determinant_zero {L : ℕ} (X : Fin 3 → ℕ) (u : Code L)
    (hdet : determinant (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2)) = 0) : Contains u X := by
  rw [determinant_eq_dot_normal, normal_valueVector_eq, dot_comm] at hdet
  change dot (planeNormal u) ((fun i ↦ (X i : ℤ)) + offsetVector (u 0)) = 0 at hdet
  rw [dot_add_right] at hdet
  unfold Contains planeConstant
  omega

theorem normal_coordinates_ne_zero {L : ℕ} (X : Fin 3 → ℕ) (u : Code L) (hx : ∀ i, 2 ≤ X i)
    (hrank : ∀ i : Fin 3, i ≠ 2 → Module.finrank F₂ (squareClassSpace (X i) L) = L)
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)))
    (hA : planeNormal u ≠ 0)
    (hdet : determinant (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2)) = 0) :
    ∀ i, planeNormal u i ≠ 0 := by
  have hAvalue : normal (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2)) ≠ 0 := by
    rw [normal_valueVector_eq X u]
    exact hA
  have hnormal := PlaneNormalRigidity.normal_coordinates_ne_zero (fun p ↦ valueVector X (u p))
    (fun p i ↦ valueVector_pos X hx (u p) i) (projection_rigid X u hx hrank hpair)
    hAvalue (plane_through_three (fun p ↦ valueVector X (u p)) hdet)
  simpa only [normal_valueVector_eq X u] using hnormal

theorem further_divisor_offset {L : ℕ} (X : Fin 3 → ℕ) (u : Code L) (hx : ∀ i, 2 ≤ X i)
    (hcontains : Contains u X) (v : Fin 3 → Fin (L + 1)) (p : ℕ)
    (hp : 12 * (L + 1) ^ 3 < p) (hdiv : ∀ i, p ∣ value (X i) (v i)) :
    dot (planeNormal u) (offsetVector v) = -planeConstant u := by
  have hvdiv (i : Fin 3) : (p : ℤ) ∣ valueVector X v i := by
    have hxpos : 0 < X i := by have h := hx i; omega
    rw [valueVector_eq_natural X v i hxpos]
    exact Int.natCast_dvd_natCast.mpr (hdiv i)
  have hdot : (p : ℤ) ∣ dot (planeNormal u) (valueVector X v) := by
    rw [dot_comm]
    exact dot_dvd_of_coordinates (p : ℤ) _ _ hvdiv
  have hid : dot (planeNormal u) (valueVector X v) = planeConstant u + dot (planeNormal u) (offsetVector v) := by
    change dot (planeNormal u) ((fun i ↦ (X i : ℤ)) + offsetVector v) = _
    rw [dot_add_right]
    exact congrArg (fun z : ℤ ↦ z + dot (planeNormal u) (offsetVector v)) hcontains
  rw [hid] at hdot
  have hbound : (planeConstant u + dot (planeNormal u) (offsetVector v)).natAbs ≤ 12 * (L + 1) ^ 3 := by
    have hconst := constant_bound u
    have hdotbound := dot_natAbs_le (planeNormal u) (offsetVector v) (2 * (L + 1) ^ 2) (L + 1)
      (normal_coordinate_bound u) (offset_natAbs_le v)
    have hadd := Int.natAbs_add_le (planeConstant u) (dot (planeNormal u) (offsetVector v))
    nlinarith
  have hz : planeConstant u + dot (planeNormal u) (offsetVector v) = 0 := by
    by_contra hne
    have hnat : p ∣ (planeConstant u + dot (planeNormal u) (offsetVector v)).natAbs := Int.natCast_dvd.mp hdot
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hnat
    omega
  omega

end PaperP1.OffsetPlaneGeometry
