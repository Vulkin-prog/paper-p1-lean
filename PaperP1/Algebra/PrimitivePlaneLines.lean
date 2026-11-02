module

public import PaperP1.Algebra.TripleCross
public import PaperP1.Algebra.PrimitiveTripleDirection

/-! # Integer line levels on a primitive plane, without choosing a lattice basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitivePlaneLines

open Finset PaperP1.TripleCross PaperP1.PrimitiveTripleDirection

theorem primitive_dot (d : Fin 3 → ℤ) : Primitive d ↔ ∃ w : Fin 3 → ℤ, dot w d = 1 := by
  simp only [Primitive, dot, Fin.sum_univ_three]

theorem cross_sub_right (a b c : Fin 3 → ℤ) : cross a (b - c) = cross a b - cross a c := by
  funext i
  fin_cases i <;> simp [cross, Pi.sub_apply] <;> ring

theorem cross_cross_right (a b c : Fin 3 → ℤ) :
    cross a (cross b c) = fun i ↦ dot a c * b i - dot a b * c i := by
  funext i
  fin_cases i <;> simp [cross, dot] <;> ring

theorem cross_cross_left (a b c : Fin 3 → ℤ) :
    cross (cross a b) c = fun i ↦ dot a c * b i - dot b c * a i := by
  funext i
  fin_cases i <;> simp [cross, dot] <;> ring

theorem cross_parallel_normal (A d v b : Fin 3 → ℤ) (hb : dot A b = 1)
    (hd : dot A d = 0) (hv : dot A v = 0) :
    cross d v = fun i ↦ dot b (cross d v) * A i := by
  have hzero : cross A (cross d v) = 0 := by
    rw [cross_cross_right]
    simp only [hv, hd, zero_mul, sub_self]
    rfl
  have hh := cross_cross_left A (cross d v) b
  rw [hzero] at hh
  have hc0 : cross (0 : Fin 3 → ℤ) b = 0 := by
    funext j
    fin_cases j <;> simp [cross]
  rw [hc0] at hh
  funext i
  have hi := congrFun hh i
  simp only [Pi.zero_apply, hb, one_mul] at hi
  rw [dot_comm (cross d v) b] at hi
  linarith only [hi]

def level (d b u : Fin 3 → ℤ) : ℤ := dot b (cross d u)

theorem level_sub (d b u v : Fin 3 → ℤ) : level d b (u - v) = level d b u - level d b v := by
  unfold level
  rw [cross_sub_right, dot_sub_right]

theorem difference_cross (A d b u v : Fin 3 → ℤ) (hb : dot A b = 1)
    (hd : dot A d = 0) (huv : dot A u = dot A v) :
    cross d (u - v) = fun i ↦ (level d b u - level d b v) * A i := by
  have hp : dot A (u - v) = 0 := by rw [dot_sub_right, huv, sub_self]
  have hh := cross_parallel_normal A d (u - v) b hb hd hp
  change cross d (u - v) = fun i ↦ level d b (u - v) * A i at hh
  simpa only [level_sub] using hh

theorem same_level_parameter (A d b u v : Fin 3 → ℤ) (hb : dot A b = 1)
    (hd : Primitive d) (hAd : dot A d = 0) (huv : dot A u = dot A v)
    (hlevel : level d b u = level d b v) :
    ∃ t : ℤ, ∀ i, u i = v i + t * d i := by
  have hc := difference_cross A d b u v hb hAd huv
  have hcross : cross d (u - v) = 0 := by
    rw [hc, hlevel]
    simp only [sub_self, zero_mul]
    rfl
  obtain ⟨t, ht⟩ := integer_multiple_of_minors d (u - v) hd
    ((cross_eq_zero_iff_minors d (u - v)).mp hcross)
  exact ⟨t, fun i ↦ by have hi := ht i; change u i - v i = _ at hi; linarith only [hi]⟩

theorem short_direction {B : ℕ} (S : Finset (Fin 3 → ℤ)) (A : Fin 3 → ℤ) (h : ℤ)
    (hcard : 1 < S.card) (hplane : ∀ u ∈ S, dot A u = h)
    (hwidth : ∀ u ∈ S, ∀ v ∈ S, ∀ i, (u i - v i).natAbs ≤ B) :
    ∃ d : Fin 3 → ℤ, Primitive d ∧ height d ≤ B ∧ dot A d = 0 := by
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp hcard
  have hw : u - v ≠ 0 := sub_ne_zero.mpr huv
  obtain ⟨g, hg, d, hd, hf⟩ := exists_primitive_direction (u - v) hw
  refine ⟨d, hd, height_le_of_factor (u - v) d g B hg hf (hwidth u hu v hv), ?_⟩
  have hzero : dot A (u - v) = 0 := by rw [dot_sub_right, hplane u hu, hplane v hv, sub_self]
  have hfactor : dot A (u - v) = (g : ℤ) * dot A d := by
    simp only [dot, hf]
    ring
  rw [hfactor] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast (show g ≠ 0 by omega))

theorem height_attained (d : Fin 3 → ℤ) : ∃ i : Fin 3, (d i).natAbs = height d := by
  by_cases h0 : max (d 1).natAbs (d 2).natAbs ≤ (d 0).natAbs
  · exact ⟨0, by simp only [height, max_eq_left h0]⟩
  · by_cases h1 : (d 2).natAbs ≤ (d 1).natAbs
    · refine ⟨1, ?_⟩
      simp only [height, max_eq_left h1]
      omega
    · refine ⟨2, ?_⟩
      unfold height
      omega

end PaperP1.PrimitivePlaneLines
