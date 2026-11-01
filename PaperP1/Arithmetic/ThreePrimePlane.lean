module

public import PaperP1.Arithmetic.OffsetPlaneGeometry

/-! # Two-prime products and the actual plane forced by three large shared primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ThreePrimePlane

open Finset PaperP1.TripleCross PaperP1.ThreeWindowRigidity PaperP1.IndexedPrimeOffsets
  PaperP1.OffsetPlaneGeometry PaperP1.OffsetLinePrimeProduct PaperP1.OffsetLinePopulation
  PaperP1.Arithmetic PaperP1.SaturationPrimes

theorem two_prime_bound {L N : ℕ} (X : Fin 3 → ℕ) (p : Fin 2 → ℕ)
    (hp : Function.Injective p) (u : Fin 2 → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hprime : ∀ i, Nat.Prime (p i)) (hdiv : ∀ i j, p i ∣ value (X j) (u i j))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L)) :
    p 0 * p 1 ≤ 6 * N * (L + 1) := by
  have h := product_le_of_collinear p hp X u hN hLN hX hprime hdiv hinj hdirect
    (pair_collinear (fun i ↦ offsetVector (u i)))
  simpa only [Fin.prod_univ_two] using h

theorem determinant_dvd_each (p : ℤ) (V : Fin 3 → Fin 3 → ℤ) (k : Fin 3)
    (hdiv : ∀ i, p ∣ V k i) : p ∣ determinant (V 0) (V 1) (V 2) := by
  fin_cases k
  · exact dot_dvd_of_coordinates p _ _ hdiv
  · rw [determinant_cyclic]
    exact dot_dvd_of_coordinates p _ _ hdiv
  · rw [determinant_cyclic, determinant_cyclic (V 1) (V 2) (V 0)]
    exact dot_dvd_of_coordinates p _ _ hdiv

theorem product_dvd_determinant {L : ℕ} (X : Fin 3 → ℕ) (hx : ∀ j, 2 ≤ X j)
    (p : Fin 3 → ℕ) (hp : Function.Injective p) (u : Code L)
    (hprime : ∀ i, Nat.Prime (p i)) (hdiv : ∀ i j, p i ∣ value (X j) (u i j)) :
    (∏ i, p i) ∣ (determinant (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2))).natAbs := by
  rw [← primeSet_prod p hp]
  apply product_dvd_of_prime_divisors (primeSet p) (primeSet_prime p hprime)
  intro q hq
  obtain ⟨i, _, rfl⟩ := mem_image.mp hq
  apply determinant_dvd_each (p i : ℤ) (fun k ↦ valueVector X (u k)) i
  intro j
  have hxpos : 0 < X j := by have h := hx j; omega
  rw [valueVector_eq_natural X (u i) j hxpos]
  exact Int.natCast_dvd_natCast.mpr (hdiv i j)

theorem determinant_zero_of_large_product {L N : ℕ} (X : Fin 3 → ℕ) (p : Fin 3 → ℕ)
    (hp : Function.Injective p) (u : Code L)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hprime : ∀ i, Nat.Prime (p i)) (hdiv : ∀ i j, p i ∣ value (X j) (u i j))
    (hlarge : 18 * N * (L + 1) ^ 2 < ∏ i, p i) :
    determinant (valueVector X (u 0)) (valueVector X (u 1)) (valueVector X (u 2)) = 0 := by
  have hx (i : Fin 3) : 2 ≤ X i := by have h := (mem_Ico.mp (hX i)).1; omega
  have hdivdet := product_dvd_determinant X hx p hp u hprime hdiv
  have hbound := determinant_bound X u hN hLN hX
  by_contra hne
  have hprod := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdivdet
  omega

theorem normal_ne_zero_of_large_product {L N : ℕ} (X : Fin 3 → ℕ) (p : Fin 3 → ℕ)
    (hp : Function.Injective p) (u : Code L)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hprime : ∀ i, Nat.Prime (p i)) (hdiv : ∀ i j, p i ∣ value (X j) (u i j))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hlarge : 18 * N * (L + 1) ^ 2 < ∏ i, p i) : planeNormal u ≠ 0 := by
  intro hzero
  have hcol := collinear_of_normal_zero (fun i ↦ offsetVector (u i)) hzero
  have hbound := product_le_of_collinear p hp X u hN hLN hX hprime hdiv hinj hdirect hcol
  have hthreshold : 6 * N * (L + 1) ≤ 18 * N * (L + 1) ^ 2 := by
    have h := Nat.mul_le_mul_left (6 * N * (L + 1)) (show 1 ≤ 3 * (L + 1) by omega)
    nlinarith [h]
  omega

/-- All finite geometric conclusions, without assuming regularity of the third window. -/
theorem forced_plane {L N : ℕ} (X : Fin 3 → ℕ) (p : Fin 3 → ℕ)
    (hp : Function.Injective p) (u : Code L)
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hprime : ∀ i, Nat.Prime (p i)) (hdiv : ∀ i j, p i ∣ value (X j) (u i j))
    (hrank : ∀ i : Fin 3, i ≠ 2 → Module.finrank F₂ (squareClassSpace (X i) L) = L)
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)))
    (hlarge : 18 * N * (L + 1) ^ 2 < ∏ i, p i) :
    planeNormal u ≠ 0 ∧ Contains u X ∧ (∀ i, planeNormal u i ≠ 0) ∧
      (∀ i, (planeNormal u i).natAbs ≤ 2 * (L + 1) ^ 2) ∧ (planeConstant u).natAbs ≤ 6 * (L + 1) ^ 3 ∧
      ∀ (q : ℕ) (v : Fin 3 → Fin (L + 1)), 12 * (L + 1) ^ 3 < q →
        (∀ i, q ∣ value (X i) (v i)) → dot (planeNormal u) (offsetVector v) = -planeConstant u := by
  have hx (i : Fin 3) : 2 ≤ X i := by have h := (mem_Ico.mp (hX i)).1; omega
  have hinj := PaperP1.TwoPointSquareClasses.injective_evenMap_of_rank (X 0) L (hrank 0 (by decide))
  have hdet := determinant_zero_of_large_product X p hp u hN hLN hX hprime hdiv hlarge
  have hA := normal_ne_zero_of_large_product X p hp u hN hLN hX hprime hdiv hinj (hpair (by decide)) hlarge
  have hcontains := contains_of_determinant_zero X u hdet
  exact ⟨hA, hcontains, normal_coordinates_ne_zero X u hx hrank hpair hA hdet,
    normal_coordinate_bound u, constant_bound u,
    fun q v hq hqdiv ↦ further_divisor_offset X u hx hcontains v q hq hqdiv⟩

end PaperP1.ThreePrimePlane
