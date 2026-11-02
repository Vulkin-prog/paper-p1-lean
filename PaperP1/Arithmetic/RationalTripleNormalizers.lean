module

public import PaperP1.Arithmetic.ScaledNormalizedIntersections
public import PaperP1.Model.PrivateNormalizedFamilyRank
public import Mathlib.Tactic.FinCases

/-! # Product normalizers and exact affine compatibility for general rational triples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleNormalizers

open Finset PaperP1.Arithmetic PaperP1.NormalizedWindowSets PaperP1.PrivateNormalizedFamilies

def physical (u v w : ℕ) : Fin 3 → ℕ := ![u, v, w]
def scale (u v w : ℕ) : Fin 3 → ℕ := ![v * w, u * w, u * v]
def centres (u v w t : ℕ) : Fin 3 → ℕ := fun i ↦ physical u v w i * t
def origin (u v w t : ℕ) : ℕ := u * v * w * t
def values (u v w t L : ℕ) (i : Fin 3) : Finset ℕ := normalized (scale u v w i) (centres u v w t i) L

theorem scale_pos {u v w : ℕ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (i : Fin 3) :
    0 < scale u v w i := by
  fin_cases i
  · exact Nat.mul_pos hv hw
  · exact Nat.mul_pos hu hw
  · exact Nat.mul_pos hu hv

theorem centres_ge_two {u v w t : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w) (ht : 1 ≤ t)
    (i : Fin 3) : 2 ≤ centres u v w t i := by
  have hphysical : 2 ≤ physical u v w i := by fin_cases i <;> norm_num [physical] <;> omega
  have hh := Nat.mul_le_mul hphysical ht
  change 2 ≤ physical u v w i * t
  simpa only [Nat.mul_one] using hh

theorem common_product (u v w t : ℕ) (i : Fin 3) :
    scale u v w i * centres u v w t i = origin u v w t := by
  fin_cases i <;> norm_num [scale, centres, physical, origin] <;> ring

theorem scale_physical (u v w : ℕ) (i : Fin 3) :
    scale u v w i * physical u v w i = u * v * w := by
  simpa only [centres, Nat.mul_one, origin] using common_product u v w 1 i

theorem predecessor_formula (u v w t : ℕ) (i : Fin 3) :
    scale u v w i * (centres u v w t i - 1) = origin u v w t - scale u v w i := by
  rw [Nat.mul_sub_left_distrib, common_product, Nat.mul_one]

theorem internal_formula (u v w t : ℕ) (i : Fin 3) (k : ℕ) :
    scale u v w i * (centres u v w t i + k) = origin u v w t + scale u v w i * k := by
  rw [Nat.mul_add, common_product]

theorem exclusive {u v w t : ℕ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 1 ≤ t) (L : ℕ) :
    Exclusive (scale u v w) (centres u v w t) L := by
  intro i j k heq
  rw [predecessor_formula, internal_formula] at heq
  have hO : 0 < origin u v w t := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hu hv) hw) (by omega)
  have hlt := Nat.sub_lt hO (scale_pos hu hv hw i)
  omega

theorem internal_mem {c x L k : ℕ} (hx : 0 < x) (hk : k < L) :
    c * (x + k) ∈ normalized c x L := by
  apply mem_image.mpr
  refine ⟨x + k, ?_, rfl⟩
  rw [values_eq_interval hx]
  exact mem_Ico.mpr ⟨by omega, by omega⟩

theorem common_mem {u v w t L : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w) (ht : 1 ≤ t)
    (hL : 1 ≤ L) (i : Fin 3) : origin u v w t ∈ values u v w t L i := by
  have hh := internal_mem (c := scale u v w i) (L := L) (k := 0)
    (show 0 < centres u v w t i by have hh := centres_ge_two hu huv hvw ht i; omega) (by omega)
  rw [Nat.add_zero, common_product] at hh
  exact hh

theorem union_three (u v w t L : ℕ) :
    valueUnion (scale u v w) (centres u v w t) L =
      ((values u v w t L 0 ∪ values u v w t L 1) ∪ values u v w t L 2) := by
  have hu : (univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [valueUnion, hu]
  simp only [biUnion_insert, singleton_biUnion, union_assoc]
  rfl

theorem pair_zero_one_upper {u v w t L : ℕ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 1 ≤ t) :
    ((values u v w t L 0 ∩ values u v w t L 1).card : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * (Nat.gcd u v : ℝ)) / v + 1 := by
  change ((normalized (v * w) (u * t) L ∩ normalized (u * w) (v * t) L).card : ℝ) ≤ _
  rw [Nat.mul_comm v w, Nat.mul_comm u w]
  exact ScaledNormalizedIntersections.reduced_intersection_bound hw hu hv
    (Nat.mul_pos hu (by omega)) (Nat.mul_pos hv (by omega))

theorem pair_zero_two_upper {u v w t L : ℕ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 1 ≤ t) :
    ((values u v w t L 0 ∩ values u v w t L 2).card : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * (Nat.gcd u w : ℝ)) / w + 1 := by
  change ((normalized (v * w) (u * t) L ∩ normalized (u * v) (w * t) L).card : ℝ) ≤ _
  rw [Nat.mul_comm u v]
  exact ScaledNormalizedIntersections.reduced_intersection_bound hv hu hw
    (Nat.mul_pos hu (by omega)) (Nat.mul_pos hw (by omega))

theorem pair_one_two_upper {u v w t L : ℕ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (ht : 1 ≤ t) :
    ((values u v w t L 1 ∩ values u v w t L 2).card : ℝ) ≤
      (((L + 1 : ℕ) : ℝ) * (Nat.gcd v w : ℝ)) / w + 1 := by
  change ((normalized (u * w) (v * t) L ∩ normalized (u * v) (w * t) L).card : ℝ) ≤ _
  exact ScaledNormalizedIntersections.reduced_intersection_bound hu hv hw
    (Nat.mul_pos hv (by omega)) (Nat.mul_pos hw (by omega))

end PaperP1.RationalTripleNormalizers
