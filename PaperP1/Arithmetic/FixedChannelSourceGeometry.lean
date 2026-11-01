module

public import PaperP1.Arithmetic.ActualSourceTranslations

/-! # Literal source separation and a polynomial baseline count for a fixed channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedChannelSourceGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.DyadicEndpointPairs

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def unitSources (N a b L : ℕ) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦ (units a b xy.1 xy.2 L).Nonempty

theorem first_projection_injective {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (i j : Fin (L + 1)) :
    Set.InjOn Prod.fst (sourcePairs N a b L i j : Set (ℕ × ℕ)) := by
  intro xy hxy uv huv heq
  obtain ⟨_, hy, hunit⟩ := mem_sourcePairs.mp hxy
  obtain ⟨_, hv, vunit⟩ := mem_sourcePairs.mp huv
  have hypos := hN.trans_le (mem_Ico.mp hy).1
  have hvpos := hN.trans_le (mem_Ico.mp hv).1
  have hlabels : startCompleteVertexLabel xy.2 L j = startCompleteVertexLabel uv.2 L j := by
    apply mul_left_cancel₀ ha.ne'
    exact hunit.symm.trans ((congrArg (fun x : ℕ ↦ b * startCompleteVertexLabel x L i) heq).trans vunit)
  rw [startCompleteVertexLabel_eq_offset hypos, startCompleteVertexLabel_eq_offset hvpos] at hlabels
  exact Prod.ext heq (by omega)

theorem source_pairs_card {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (i j : Fin (L + 1)) :
    (sourcePairs N a b L i j).card ≤ N := by
  have hc : (sourcePairs N a b L i j).card ≤ (dyadicBlock N).card := by
    apply card_le_card_of_injOn Prod.fst
    · intro xy hxy
      exact (mem_sourcePairs.mp hxy).1
    · exact first_projection_injective hN ha i j
  have hcard : (dyadicBlock N).card = N := by unfold dyadicBlock; rw [Nat.card_Ico]; omega
  exact hc.trans (le_of_eq hcard)

theorem unit_sources_card {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) :
    (unitSources N a b L).card ≤ (L + 1) ^ 2 * N := by
  have hsub : unitSources N a b L ⊆ univ.biUnion (fun ij : Fin (L + 1) × Fin (L + 1) ↦
      sourcePairs N a b L ij.1 ij.2) := by
    intro xy hxy
    obtain ⟨hblock, u, hu⟩ := mem_filter.mp hxy
    have hb := mem_product.mp hblock
    exact mem_biUnion.mpr ⟨u, mem_univ _, mem_sourcePairs.mpr ⟨hb.1, hb.2, mem_units.mp hu⟩⟩
  calc
    _ ≤ (univ.biUnion (fun ij : Fin (L + 1) × Fin (L + 1) ↦ sourcePairs N a b L ij.1 ij.2)).card :=
      card_le_card hsub
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), (sourcePairs N a b L ij.1 ij.2).card := card_biUnion_le
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), N := sum_le_sum (fun ij _ ↦ source_pairs_card hN ha ij.1 ij.2)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]; ring

theorem source_separated {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b) (hcop : a.Coprime b)
    (hlarge : (a + b) * (L + 1) < N) (i j : Fin (L + 1)) {xy : ℕ × ℕ}
    (hxy : xy ∈ sourcePairs N a b L i j) : xy.1 + L ≤ xy.2 := by
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
  have hj := j.isLt
  omega

end PaperP1.FixedChannelSourceGeometry
