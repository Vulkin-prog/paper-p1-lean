module

public import PaperP1.Arithmetic.TernaryGroupForcedPlane
public import Mathlib.Data.Fintype.BigOperators

/-! # The forced ternary planes belong to an explicit pool independent of the centers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryOffsetPlanes

open Finset PaperP1.Arithmetic PaperP1.TernaryPrimeGroups PaperP1.FiniteEvenSquareClasses
  PaperP1.TernaryGroupDeterminants PaperP1.TernaryGroupForcedPlane PaperP1.TripleCross

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def offsetNormal (X : Fin 3 → ℤ) (u v w : Fin 3 → ℕ) : Fin 3 → ℤ :=
  normal (vector u - X) (vector v - X) (vector w - X)

def planeConstant (X : Fin 3 → ℤ) (u v w : Fin 3 → ℕ) : ℤ :=
  -dot (offsetNormal X u v w) (vector u - X)

def planePool (R : ℕ) : Finset ((Fin 3 → ℤ) × ℤ) :=
  (Fintype.piFinset fun _ : Fin 3 ↦ Icc (-((8 * R ^ 2 : ℕ) : ℤ)) ((8 * R ^ 2 : ℕ) : ℤ)) ×ˢ
    Icc (-((24 * R ^ 3 : ℕ) : ℤ)) ((24 * R ^ 3 : ℕ) : ℤ)

theorem offsetNormal_eq_value (X : Fin 3 → ℤ) (u v w : Fin 3 → ℕ) :
    offsetNormal X u v w = normal (vector u) (vector v) (vector w) := by
  have hv : (vector v - X) - (vector u - X) = vector v - vector u := by abel
  have hw : (vector w - X) - (vector u - X) = vector w - vector u := by abel
  unfold offsetNormal normal
  rw [hv, hw]

theorem width_of_offset_bounds {U : Fin 3 → Finset ℕ} {X : Fin 3 → ℤ} {R H : ℕ}
    (hbound : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R) (hRH : 2 * R ≤ H) :
    ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H := by
  intro i n hn m hm
  have heq : (n : ℤ) - m = ((n : ℤ) - X i) - ((m : ℤ) - X i) := by ring
  rw [heq]
  exact ((Int.natAbs_sub_le _ _).trans (Nat.add_le_add (hbound i n hn) (hbound i m hm))).trans (by omega)

theorem offsetNormal_bound (X : Fin 3 → ℤ) (u v w : Fin 3 → ℕ) (R : ℕ)
    (hu : ∀ i, (vector u i - X i).natAbs ≤ R)
    (hv : ∀ i, (vector v i - X i).natAbs ≤ R)
    (hw : ∀ i, (vector w i - X i).natAbs ≤ R) (i : Fin 3) :
    (offsetNormal X u v w i).natAbs ≤ 8 * R ^ 2 := by
  have hdv (j : Fin 3) : (((vector v - X) - (vector u - X)) j).natAbs ≤ 2 * R := by
    have h := (Int.natAbs_sub_le (vector v j - X j) (vector u j - X j)).trans (Nat.add_le_add (hv j) (hu j))
    simpa only [Pi.sub_apply, two_mul] using h
  have hdw (j : Fin 3) : (((vector w - X) - (vector u - X)) j).natAbs ≤ 2 * R := by
    have h := (Int.natAbs_sub_le (vector w j - X j) (vector u j - X j)).trans (Nat.add_le_add (hw j) (hu j))
    simpa only [Pi.sub_apply, two_mul] using h
  calc
    _ ≤ 2 * (2 * R) * (2 * R) := cross_coordinate_natAbs_le _ _ (2 * R) (2 * R) hdv hdw i
    _ = _ := by ring

theorem planeConstant_bound (X : Fin 3 → ℤ) (u v w : Fin 3 → ℕ) (R : ℕ)
    (hu : ∀ i, (vector u i - X i).natAbs ≤ R)
    (hv : ∀ i, (vector v i - X i).natAbs ≤ R)
    (hw : ∀ i, (vector w i - X i).natAbs ≤ R) :
    (planeConstant X u v w).natAbs ≤ 24 * R ^ 3 := by
  have h := dot_natAbs_le (offsetNormal X u v w) (vector u - X) (8 * R ^ 2) R
    (offsetNormal_bound X u v w R hu hv hw) hu
  rw [planeConstant, Int.natAbs_neg]
  nlinarith only [h]

theorem centers_on_plane {X : Fin 3 → ℤ} {u v w : Fin 3 → ℕ}
    (hdet : determinant (vector u) (vector v) (vector w) = 0) :
    dot (offsetNormal X u v w) X = planeConstant X u v w := by
  have hz : dot (offsetNormal X u v w) (vector u) = 0 := by
    rw [offsetNormal_eq_value, dot_comm, ← determinant_eq_dot_normal]
    exact hdet
  rw [planeConstant, dot_sub_right, hz]
  ring

theorem mem_planePool (X : Fin 3 → ℤ) (u v w : Fin 3 → ℕ) (R : ℕ)
    (hu : ∀ i, (vector u i - X i).natAbs ≤ R)
    (hv : ∀ i, (vector v i - X i).natAbs ≤ R)
    (hw : ∀ i, (vector w i - X i).natAbs ≤ R) :
    (offsetNormal X u v w, planeConstant X u v w) ∈ planePool R := by
  apply mem_product.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro i
    have h : |offsetNormal X u v w i| ≤ ((8 * R ^ 2 : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast offsetNormal_bound X u v w R hu hv hw i
    exact mem_Icc.mpr (abs_le.mp h)
  · have h : |planeConstant X u v w| ≤ ((24 * R ^ 3 : ℕ) : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast planeConstant_bound X u v w R hu hv hw
    exact mem_Icc.mpr (abs_le.mp h)

theorem planePool_card (R : ℕ) : (planePool R).card = (16 * R ^ 2 + 1) ^ 3 * (48 * R ^ 3 + 1) := by
  have hbox (A : ℕ) : (Icc (-(A : ℤ)) (A : ℤ)).card = 2 * A + 1 := by rw [Int.card_Icc]; omega
  rw [planePool, card_product, Fintype.card_piFinset_const, hbox, hbox]
  ring

theorem forced_offset_plane {U : Fin 3 → Finset ℕ} {X : Fin 3 → ℤ} {A H R : ℕ} (hH : 1 ≤ H)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    (hbox : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    {u v w : Fin 3 → ℕ} (hu : u ∈ supportPool U) (hv : v ∈ supportPool U) (hw : w ∈ supportPool U)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hlarge : 6 * A * H ^ 2 < group H u * group H v * group H w) :
    ∃ P ∈ planePool R, P.1 ≠ 0 ∧ (∀ i, P.1 i ≠ 0) ∧ dot P.1 X = P.2 := by
  have hforced := forced_plane hH hwidth hpos hmax hinj hdirect hu hv hw huv huw hvw hlarge
  have hum (i : Fin 3) : (vector u i - X i).natAbs ≤ R := hbox i (u i) ((mem_supportPool U u).mp hu i)
  have hvm (i : Fin 3) : (vector v i - X i).natAbs ≤ R := hbox i (v i) ((mem_supportPool U v).mp hv i)
  have hwm (i : Fin 3) : (vector w i - X i).natAbs ≤ R := hbox i (w i) ((mem_supportPool U w).mp hw i)
  refine ⟨(offsetNormal X u v w, planeConstant X u v w), mem_planePool X u v w R hum hvm hwm, ?_, ?_, ?_⟩
  · exact (offsetNormal_eq_value X u v w) ▸ hforced.1
  · intro i
    rw [offsetNormal_eq_value]
    exact hforced.2.2.1 i
  · exact centers_on_plane (determinant_zero_of_large_groups hwidth hmax hu hv hw hlarge)

end PaperP1.TernaryOffsetPlanes
