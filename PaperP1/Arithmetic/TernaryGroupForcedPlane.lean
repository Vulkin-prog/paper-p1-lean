module

public import PaperP1.Arithmetic.TernaryGroupDeterminants
public import PaperP1.Algebra.PrimitivePlaneLines

/-! # Three large actual groups force a genuine plane by an unnormalized cross difference -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryGroupForcedPlane

open Finset PaperP1.Arithmetic PaperP1.TernaryPrimeGroups PaperP1.FiniteEvenSquareClasses
  PaperP1.FiniteEvenSetRigidity PaperP1.TernaryGroupDeterminants PaperP1.TripleCross
  PaperP1.PrimitivePlaneLines

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem cross_dvd_right (p : ℤ) (a b : Fin 3 → ℤ) (hb : ∀ i, p ∣ b i) (i : Fin 3) :
    p ∣ cross a b i := by
  have hpair (j k : Fin 3) : p ∣ a j * b k - a k * b j := dvd_sub
    (dvd_mul_of_dvd_right (hb k) (a j)) (dvd_mul_of_dvd_right (hb j) (a k))
  fin_cases i
  · simpa [cross] using hpair 1 2
  · simpa [cross] using hpair 2 0
  · simpa [cross] using hpair 0 1

theorem cross_difference_first (a b : Fin 3 → ℤ) : cross (b - a) a = cross (b - a) b := by
  funext i
  fin_cases i <;> simp [cross, Pi.sub_apply] <;> ring

theorem collinear_group_product_dvd {U : Fin 3 → Finset ℕ} {H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    {u v w : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (hw : w ∈ supportPool U)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hcol : normal (vector u) (vector v) (vector w) = 0) (i : Fin 3) :
    group H u * group H v * group H w ∣ (cross (vector v - vector u) (vector u) i).natAbs := by
  let d := vector v - vector u
  have hthird : cross d (vector w) = cross d (vector u) := by
    change cross d (vector w - vector u) = 0 at hcol
    rw [cross_sub_right] at hcol
    exact sub_eq_zero.mp hcol
  have hdu : group H u ∣ (cross d (vector u) i).natAbs := Int.natCast_dvd.mp
    (cross_dvd_right (group H u) d (vector u)
      (fun j ↦ Int.natCast_dvd_natCast.mpr (group_dvd_value H u j)) i)
  have hdv : group H v ∣ (cross d (vector u) i).natAbs := by
    rw [cross_difference_first]
    exact Int.natCast_dvd.mp (cross_dvd_right (group H v) d (vector v)
      (fun j ↦ Int.natCast_dvd_natCast.mpr (group_dvd_value H v j)) i)
  have hdw : group H w ∣ (cross d (vector u) i).natAbs := by
    rw [← hthird]
    exact Int.natCast_dvd.mp (cross_dvd_right (group H w) d (vector w)
      (fun j ↦ Int.natCast_dvd_natCast.mpr (group_dvd_value H w j)) i)
  have hcop : Nat.Coprime (group H u * group H v) (group H w) := Nat.coprime_mul_iff_left.mpr
    ⟨group_coprime hwidth hu hw huw, group_coprime hwidth hv hw hvw⟩
  exact hcop.mul_dvd_of_dvd_of_dvd
    ((group_coprime hwidth hu hv huv).mul_dvd_of_dvd_of_dvd hdu hdv) hdw

theorem normal_nonzero_of_large_groups {U : Fin 3 → Finset ℕ} {A H : ℕ}
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    {u v w : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (hw : w ∈ supportPool U)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hlarge : 2 * A * H < group H u * group H v * group H w) :
    normal (vector u) (vector v) (vector w) ≠ 0 := by
  intro hcol
  have hum := (mem_supportPool U u).mp hu
  have hvm := (mem_supportPool U v).mp hv
  have hcross : cross (vector v - vector u) (vector u) = 0 := by
    funext i
    by_contra hne
    have hdiv := collinear_group_product_dvd hwidth hu hv hw huv huw hvw hcol i
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) hdiv
    have hbound := cross_coordinate_natAbs_le (vector v - vector u) (vector u) H A
      (fun j ↦ hwidth j (v j) (hvm j) (u j) (hum j))
      (fun j ↦ by simpa only [vector, Int.natAbs_natCast] using hmax j (u j) (hum j)) i
    nlinarith only [hle, hbound, hlarge]
  have hproducts (i j : Fin 3) : u i * v j = v i * u j := by
    have h := (cross_eq_zero_iff_minors _ _).mp hcross i j
    change ((v i : ℤ) - u i) * (u j : ℤ) = ((v j : ℤ) - u j) * (u i : ℤ) at h
    have hcrossZ : (u i : ℤ) * v j = (v i : ℤ) * u j := by nlinarith only [h]
    exact_mod_cast hcrossZ
  have hequal (i j : Fin 3) (hij : i ≠ j) : u i = v i :=
    projection_equal (hinj i) (hdirect hij) (hum i) (hvm i) (hum j) (hvm j)
      (hpos i _ (hum i)) (hpos i _ (hvm i)) (hpos j _ (hum j)) (hpos j _ (hvm j)) (hproducts i j)
  apply huv
  funext i
  fin_cases i
  · exact hequal 0 1 (by decide)
  · exact hequal 1 0 (by decide)
  · exact hequal 2 0 (by decide)

theorem forced_plane {U : Fin 3 → Finset ℕ} {A H : ℕ} (hH : 1 ≤ H)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    {u v w : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (hw : w ∈ supportPool U)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hlarge : 6 * A * H ^ 2 < group H u * group H v * group H w) :
    normal (vector u) (vector v) (vector w) ≠ 0 ∧
      (∀ i, (normal (vector u) (vector v) (vector w) i).natAbs ≤ 2 * H ^ 2) ∧
      (∀ i, normal (vector u) (vector v) (vector w) i ≠ 0) ∧
      (∀ p : Fin 3, dot (normal (vector u) (vector v) (vector w)) (vector (![u, v, w] p)) = 0) := by
  have hdet := determinant_zero_of_large_groups hwidth hmax hu hv hw hlarge
  have hH2 : H ≤ H ^ 2 := le_self_pow₀ hH (by decide : 2 ≠ 0)
  have hsmall : 2 * A * H ≤ 6 * A * H ^ 2 := by
    have h := Nat.mul_le_mul_left (2 * A) hH2
    nlinarith only [h, Nat.zero_le (A * H ^ 2)]
  have hnormal := normal_nonzero_of_large_groups hwidth hpos hmax hinj hdirect hu hv hw huv huw hvw (hsmall.trans_lt hlarge)
  have hum := (mem_supportPool U u).mp hu
  have hvm := (mem_supportPool U v).mp hv
  have hwm := (mem_supportPool U w).mp hw
  have hbound (i : Fin 3) : (normal (vector u) (vector v) (vector w) i).natAbs ≤ 2 * H ^ 2 := by
    have h := cross_coordinate_natAbs_le (vector v - vector u) (vector w - vector u) H H
      (fun j ↦ hwidth j (v j) (hvm j) (u j) (hum j))
      (fun j ↦ hwidth j (w j) (hwm j) (u j) (hum j)) i
    simpa only [normal, pow_two, mul_assoc] using h
  let V : Fin 3 → Fin 3 → ℕ := ![u, v, w]
  have hmem : ∀ p i, V p i ∈ U i := by
    intro p i
    fin_cases p
    · exact hum i
    · exact hvm i
    · exact hwm i
  have hpositive : ∀ p i, 0 < vector (V p) i := by
    intro p i
    change 0 < (V p i : ℤ)
    exact_mod_cast hpos i (V p i) (hmem p i)
  have hrigid := FiniteEvenSetRigidity.projection_rigid U V hinj hdirect hmem (fun p i ↦ hpos i (V p i) (hmem p i))
  have hplane := plane_through_three (fun p ↦ vector (V p)) hdet
  have hcoordinates := PlaneNormalRigidity.normal_coordinates_ne_zero (fun p ↦ vector (V p)) hpositive hrigid hnormal hplane
  exact ⟨hnormal, hbound, hcoordinates, hplane⟩

end PaperP1.TernaryGroupForcedPlane
