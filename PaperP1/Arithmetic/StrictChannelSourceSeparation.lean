module

public import PaperP1.Arithmetic.FixedChannelSourceGeometry

/-! # Actual nontrivial channel source pairs are strictly separated -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrictChannelSourceSeparation

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.DyadicEndpointPairs PaperP1.NormalizedUnitCount

theorem source_strictly_separated {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a)
    (hab : a < b) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N)
    (i j : Fin (L + 1)) {xy : ℕ × ℕ} (hxy : xy ∈ sourcePairs N a b L i j) :
    xy.1 + L < xy.2 := by
  obtain ⟨hx, hy, hunit⟩ := mem_sourcePairs.mp hxy
  have hx2 : 2 ≤ xy.1 := hN.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ xy.2 := hN.trans (mem_Ico.mp hy).1
  obtain ⟨t, _, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop hx2 i j hunit
  rw [startCompleteVertexLabel_eq_offset (by omega)] at hbaseX hbaseY
  have hstart : (a + b) * (L + 1) ≤ xy.1 - 1 := by have := (mem_Ico.mp hx).1; omega
  have hcoeff : 2 * a ≤ a + b := by omega
  have hcoeffMul := Nat.mul_le_mul_right (L + 1) hcoeff
  have hmul : a * (2 * (L + 1)) ≤ a * t := by nlinarith only [hstart, hbaseX, hcoeffMul]
  have ht : 2 * (L + 1) ≤ t := Nat.le_of_mul_le_mul_left hmul ha
  have habt : a * t + t ≤ b * t := by
    have hm := Nat.mul_le_mul_right t (by omega : a + 1 ≤ b)
    nlinarith only [hm]
  have hi := i.isLt
  have hj := j.isLt
  omega

end PaperP1.StrictChannelSourceSeparation
