module

public import PaperP1.Arithmetic.OffsetLineData

/-! # Whole prime products on actual collinear offset configurations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OffsetLinePrimeProduct

open Finset PaperP1.OffsetLineData PaperP1.IntegralLine PaperP1.PrimitiveTripleDirection
  PaperP1.SaturationPrimes PaperP1.Arithmetic

variable {P : Finset ℕ} {L N : ℕ}

theorem product_dvd_of_prime_divisors (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (c : ℤ)
    (hdiv : ∀ p ∈ P, (p : ℤ) ∣ c) : P.prod id ∣ c.natAbs := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
  · intro p hp
    exact Int.natCast_dvd.mp (hdiv p hp)

theorem value_natAbs_le (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N)) (a : P) (i : Fin 3) :
    (values X u a i).natAbs ≤ 3 * N := by
  have hx : 0 < X i := by have h := (mem_Ico.mp (hX i)).1; omega
  rw [values_eq_natural X u a i hx, Int.natAbs_natCast]
  exact (value_bounds hN hLN (hX i) (u a i)).2

theorem cross_natAbs_le (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (a : P) (d : Fin 3 → ℤ) (i j : Fin 3) :
    (d i * values X u a j - d j * values X u a i).natAbs ≤ 6 * N * height d := by
  calc
    _ ≤ (d i * values X u a j).natAbs + (d j * values X u a i).natAbs := Int.natAbs_sub_le _ _
    _ = (d i).natAbs * (values X u a j).natAbs + (d j).natAbs * (values X u a i).natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
    _ ≤ height d * (3 * N) + height d * (3 * N) := Nat.add_le_add
      (Nat.mul_le_mul (coordinate_natAbs_le_height d i) (value_natAbs_le X u hN hLN hX a j))
      (Nat.mul_le_mul (coordinate_natAbs_le_height d j) (value_natAbs_le X u hN hLN hX a i))
    _ = _ := by ring

theorem product_dvd_cross (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hX : ∀ i, 0 < X i) (hP : ∀ p ∈ P, Nat.Prime p)
    (hdiv : ∀ p : P, ∀ i, p.val ∣ value (X i) (u p i))
    (a : P) (d : Fin 3 → ℤ)
    (hparam : ∀ p : P, ∃ t : ℤ, ∀ i, point u p i = point u a i + t * d i) (i j : Fin 3) :
    P.prod id ∣ (d i * values X u a j - d j * values X u a i).natAbs := by
  apply product_dvd_of_prime_divisors P hP
  intro p hp
  let q : P := ⟨p, hp⟩
  obtain ⟨t, ht⟩ := hparam q
  rw [← cross_constant X u a q d t ht i j]
  have hi : (p : ℤ) ∣ values X u q i := by
    rw [values_eq_natural X u q i (hX i)]
    exact Int.natCast_dvd_natCast.mpr (hdiv q i)
  have hj : (p : ℤ) ∣ values X u q j := by
    rw [values_eq_natural X u q j (hX j)]
    exact Int.natCast_dvd_natCast.mpr (hdiv q j)
  exact (dvd_mul_of_dvd_right hj (d i)).sub (dvd_mul_of_dvd_right hi (d j))

theorem single_point_product_bound (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hP : ∀ p ∈ P, Nat.Prime p) (hdiv : ∀ p : P, ∀ i, p.val ∣ value (X i) (u p i))
    (hsize : (points u).card ≤ 1) : P.prod id ≤ 3 * N := by
  classical
  rcases P.eq_empty_or_nonempty with hEmpty | ⟨p, hp⟩
  · simp only [hEmpty, prod_empty]
    omega
  let a : P := ⟨p, hp⟩
  have hXpos (i : Fin 3) : 0 < X i := by have h := (mem_Ico.mp (hX i)).1; omega
  have hdivprod : P.prod id ∣ (values X u a 0).natAbs := by
    apply product_dvd_of_prime_divisors P hP
    intro q hq
    let b : P := ⟨q, hq⟩
    have heq : point u b = point u a := card_le_one.mp hsize _ (mem_image.mpr ⟨b, mem_univ _, rfl⟩)
      _ (mem_image.mpr ⟨a, mem_univ _, rfl⟩)
    have hval : values X u b 0 = values X u a 0 := by unfold values; rw [heq]
    rw [← hval, values_eq_natural X u b 0 (hXpos 0)]
    exact Int.natCast_dvd_natCast.mpr (hdiv b 0)
  have hvalpos : 0 < (values X u a 0).natAbs := by
    rw [values_eq_natural X u a 0 (hXpos 0), Int.natAbs_natCast]
    exact (value_bounds hN hLN (hX 0) (u a 0)).1
  exact (Nat.le_of_dvd hvalpos hdivprod).trans (value_natAbs_le X u hN hLN hX a 0)

theorem line_product_bound (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hP : ∀ p ∈ P, Nat.Prime p) (hdiv : ∀ p : P, ∀ i, p.val ∣ value (X i) (u p i))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hcol : Collinear (point u)) (hsize : 1 < (points u).card) :
    ∃ a b : P, point u a ≠ point u b ∧ ∃ d : Fin 3 → ℤ,
      Primitive d ∧ height d ≤ L + 1 ∧
      (∀ p : P, ∃ t : ℤ, ∀ i, point u p i = point u a i + t * d i) ∧
      P.prod id ≤ 6 * N * height d := by
  obtain ⟨a, b, hab, d, hd, hheight, hparam⟩ := exists_direction u hcol hsize
  have hX2 (i : Fin 3) : 2 ≤ X i := by have h := (mem_Ico.mp (hX i)).1; omega
  obtain ⟨i, j, hnonzero⟩ := exists_nonzero_cross X u hX2 hinj hdirect a b hab d hd hparam
  have hprod := product_dvd_cross X u (fun i ↦ by have h := hX2 i; omega) hP hdiv a d hparam i j
  have habspos : 0 < (d i * values X u a j - d j * values X u a i).natAbs :=
    Int.natAbs_pos.mpr hnonzero
  refine ⟨a, b, hab, d, hd, hheight, hparam, ?_⟩
  exact (Nat.le_of_dvd habspos hprod).trans (cross_natAbs_le X u hN hLN hX a d i j)

theorem product_le_uniform (X : Fin 3 → ℕ) (u : P → Fin 3 → Fin (L + 1))
    (hN : 10 ≤ N) (hLN : L + 1 ≤ N + 1) (hX : ∀ i, X i ∈ Ico N (2 * N))
    (hP : ∀ p ∈ P, Nat.Prime p) (hdiv : ∀ p : P, ∀ i, p.val ∣ value (X i) (u p i))
    (hinj : Function.Injective (evenSquareClassMap (X 0) L))
    (hdirect : Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L))
    (hcol : Collinear (point u)) : P.prod id ≤ 6 * N * (L + 1) := by
  by_cases hsize : (points u).card ≤ 1
  · have h := single_point_product_bound X u hN hLN hX hP hdiv hsize
    nlinarith
  · obtain ⟨_, _, _, d, _, hheight, _, hbound⟩ := line_product_bound X u hN hLN hX hP hdiv hinj hdirect hcol (by omega)
    exact hbound.trans (Nat.mul_le_mul_left (6 * N) hheight)

end PaperP1.OffsetLinePrimeProduct
