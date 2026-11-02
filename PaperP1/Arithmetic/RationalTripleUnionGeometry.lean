module

public import PaperP1.Arithmetic.RationalTripleNormalizers

/-! # A single short interval contains the complete merged normalized rational triple -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalTripleUnionGeometry

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.PrivateNormalizedFamilies PaperP1.RationalTripleNormalizers

theorem scale_le_square {u v w Q : ℕ} (huv : u ≤ v) (hvw : v ≤ w) (hwQ : w ≤ Q) (i : Fin 3) :
    scale u v w i ≤ Q ^ 2 := by
  have huQ := huv.trans (hvw.trans hwQ)
  have hvQ := hvw.trans hwQ
  fin_cases i
  · change v * w ≤ Q ^ 2
    simpa only [pow_two] using Nat.mul_le_mul hvQ hwQ
  · change u * w ≤ Q ^ 2
    simpa only [pow_two] using Nat.mul_le_mul huQ hwQ
  · change u * v ≤ Q ^ 2
    simpa only [pow_two] using Nat.mul_le_mul huQ hvQ

theorem union_bounds {u v w t L Q : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hwQ : w ≤ Q) (ht : 1 ≤ t) (n : ℕ)
    (hn : n ∈ valueUnion (scale u v w) (centres u v w t) L) :
    origin u v w t ≤ n + Q ^ 2 * (L + 1) ∧ n ≤ origin u v w t + Q ^ 2 * (L + 1) := by
  obtain ⟨i, _, hn⟩ := mem_biUnion.mp hn
  obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
  have hx := centres_ge_two hu huv hvw ht i
  have hmI := mem_Ico.mp ((values_eq_interval (by omega : 0 < centres u v w t i)).symm ▸ hm)
  have hlow := Nat.mul_le_mul_left (scale u v w i) (show centres u v w t i ≤ m + 1 by omega)
  have hhigh := Nat.mul_le_mul_left (scale u v w i) (show m ≤ centres u v w t i + L by omega)
  rw [Nat.mul_add, Nat.mul_one, common_product] at hlow
  rw [Nat.mul_add, common_product] at hhigh
  have hs := scale_le_square huv hvw hwQ i
  have hstep : scale u v w i ≤ Q ^ 2 * (L + 1) :=
    hs.trans (by nlinarith only [Nat.zero_le (Q ^ 2 * L)])
  have hlength := Nat.mul_le_mul hs (show L ≤ L + 1 by omega)
  exact ⟨by omega, by omega⟩

theorem origin_bounds {N u v w t Q : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w) (hwQ : w ≤ Q)
    (hx : u * t ∈ dyadicBlock N) : N ≤ origin u v w t ∧ origin u v w t ≤ 2 * Q ^ 2 * N := by
  have hprod : v * w ≤ Q ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul (hvw.trans hwQ) hwQ
  have hpos : 1 ≤ v * w := by
    have hv : 1 ≤ v := by omega
    have hw : 1 ≤ w := by omega
    nlinarith
  have heq : origin u v w t = (v * w) * (u * t) := by unfold origin; ring
  rw [heq]
  have hlow : u * t ≤ (v * w) * (u * t) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (u * t) hpos
  have hhigh := Nat.mul_le_mul hprod (mem_Ico.mp hx).2.le
  constructor
  · exact (mem_Ico.mp hx).1.trans hlow
  · nlinarith only [hhigh]

theorem interval_data {N u v w t L Q : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) (hvw : v ≤ w)
    (hwQ : w ≤ Q) (ht : 1 ≤ t) (hx : u * t ∈ dyadicBlock N) (hthin : 8 * Q ^ 2 * (L + 1) ≤ N) :
    let U := origin u v w t - Q ^ 2 * (L + 1)
    valueUnion (scale u v w) (centres u v w t) L ⊆ Icc U (U + 2 * Q ^ 2 * (L + 1)) ∧
      N ≤ 2 * U ∧ U ≤ 2 * Q ^ 2 * N := by
  dsimp only
  have horigin := origin_bounds hu huv hvw hwQ hx
  have hsize : Q ^ 2 * (L + 1) ≤ origin u v w t := by nlinarith only [hthin, horigin.1]
  have hcancel := Nat.sub_add_cancel hsize
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hh := union_bounds hu huv hvw hwQ ht n hn
    apply mem_Icc.mpr
    constructor
    · omega
    · nlinarith only [hcancel, hh.2]
  · nlinarith only [hcancel, hthin, horigin.1]
  · exact (Nat.sub_le _ _).trans horigin.2

end PaperP1.RationalTripleUnionGeometry
