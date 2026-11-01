module

public import PaperP1.Arithmetic.ActualDyadicInterior
public import Mathlib.Data.Int.Interval

/-! # Explicit finite counts for actual source pairs near either dyadic endpoint -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicEndpointPairs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

local instance endpointDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem integer_interval_card (A R : ℕ) :
    (Icc ((A : ℤ) - R) ((A : ℤ) + R)).card = 2 * R + 1 := by
  rw [Int.card_Icc]
  have h : (A : ℤ) + R + 1 - ((A : ℤ) - R) = ((2 * R + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

theorem endpoint_filter_card {α : Type*} [DecidableEq α] (T : Finset α) (label : α → ℕ)
    (q M R : ℕ) (hinj : Set.InjOn (fun u ↦ q * label u) (T : Set α)) :
    (T.filter fun u ↦ |(label u : ℤ) - M| ≤ R).card ≤ 2 * q * R + 1 := by
  have hcard : (T.filter fun u ↦ |(label u : ℤ) - M| ≤ R).card ≤
      (Icc (((q * M : ℕ) : ℤ) - (q * R : ℕ)) (((q * M : ℕ) : ℤ) + (q * R : ℕ))).card := by
    apply card_le_card_of_injOn (fun u ↦ ((q * label u : ℕ) : ℤ))
    · intro u hu
      have hbound := (mem_filter.mp hu).2
      have hscale : |((q * label u : ℕ) : ℤ) - ((q * M : ℕ) : ℤ)| ≤ ((q * R : ℕ) : ℤ) := by
        push_cast
        rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) q)]
        exact mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (α := ℤ) q)
      obtain ⟨hlo, hhi⟩ := abs_le.mp hscale
      apply mem_Icc.mpr
      constructor <;> linarith only [hlo, hhi]
    · intro u hu v hv heq
      change ((q * label u : ℕ) : ℤ) = ((q * label v : ℕ) : ℤ) at heq
      have heqN : q * label u = q * label v := by exact_mod_cast heq
      exact hinj (mem_filter.mp hu).1 (mem_filter.mp hv).1 heqN
  rw [integer_interval_card] at hcard
  nlinarith only [hcard]

def sourcePairs (N a b L : ℕ) (i j : Fin (L + 1)) : Finset (ℕ × ℕ) :=
  ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun xy ↦
    b * startCompleteVertexLabel xy.1 L i = a * startCompleteVertexLabel xy.2 L j

theorem mem_sourcePairs {N a b L : ℕ} {i j : Fin (L + 1)} {xy : ℕ × ℕ} :
    xy ∈ sourcePairs N a b L i j ↔ xy.1 ∈ dyadicBlock N ∧ xy.2 ∈ dyadicBlock N ∧
      b * startCompleteVertexLabel xy.1 L i = a * startCompleteVertexLabel xy.2 L j := by
  simp only [sourcePairs, mem_filter, mem_product, and_assoc]

theorem first_anchor_injective {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) :
    Set.InjOn (fun xy : ℕ × ℕ ↦ b * startCompleteVertexLabel xy.1 L i) (sourcePairs N a b L i j) := by
  intro xy hxy xy' hxy' heq
  obtain ⟨hx, hy, hu⟩ := mem_sourcePairs.mp hxy
  obtain ⟨hx', hy', hu'⟩ := mem_sourcePairs.mp hxy'
  exact NormalizedMotifs.anchor_injective ha hb i j
    ⟨hN.trans_le (mem_Ico.mp hx).1, hN.trans_le (mem_Ico.mp hy).1, hu⟩
    ⟨hN.trans_le (mem_Ico.mp hx').1, hN.trans_le (mem_Ico.mp hy').1, hu'⟩ heq

theorem second_anchor_injective {N a b L : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b)
    (i j : Fin (L + 1)) :
    Set.InjOn (fun xy : ℕ × ℕ ↦ a * startCompleteVertexLabel xy.2 L j) (sourcePairs N a b L i j) := by
  intro xy hxy xy' hxy' heq
  have hu := (mem_sourcePairs.mp hxy).2.2
  have hu' := (mem_sourcePairs.mp hxy').2.2
  exact first_anchor_injective hN ha hb i j hxy hxy' (hu.trans (heq.trans hu'.symm))

def first (N a b L R : ℕ) (i j : Fin (L + 1)) : Finset (ℕ × ℕ) :=
  (sourcePairs N a b L i j).filter fun xy ↦ |(startCompleteVertexLabel xy.1 L i : ℤ) - N| ≤ R

def second (N a b L R : ℕ) (i j : Fin (L + 1)) : Finset (ℕ × ℕ) :=
  (sourcePairs N a b L i j).filter fun xy ↦ |(startCompleteVertexLabel xy.2 L j : ℤ) - 2 * N| ≤ R

def exceptional (N a b L R : ℕ) : Finset (ℕ × ℕ) :=
  univ.biUnion fun ij : Fin (L + 1) × Fin (L + 1) ↦ first N a b L R ij.1 ij.2 ∪ second N a b L R ij.1 ij.2

theorem first_card {N a b L R : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) (i j : Fin (L + 1)) :
    (first N a b L R i j).card ≤ 2 * b * R + 1 := by
  have h := endpoint_filter_card (sourcePairs N a b L i j) (fun xy : ℕ × ℕ ↦ startCompleteVertexLabel xy.1 L i)
    b N R (first_anchor_injective hN ha hb i j)
  simpa only [first] using h

theorem second_card {N a b L R : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) (i j : Fin (L + 1)) :
    (second N a b L R i j).card ≤ 2 * a * R + 1 := by
  have h := endpoint_filter_card (sourcePairs N a b L i j) (fun xy ↦ startCompleteVertexLabel xy.2 L j)
    a (2 * N) R (second_anchor_injective hN ha hb i j)
  simpa only [second, Nat.cast_mul, Nat.cast_ofNat] using h

theorem exceptional_card {N a b L R : ℕ} (hN : 0 < N) (ha : 0 < a) (hb : 0 < b) :
    (exceptional N a b L R).card ≤ (L + 1) ^ 2 * (2 * (a + b) * R + 2) := by
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1), (first N a b L R ij.1 ij.2 ∪ second N a b L R ij.1 ij.2).card := card_biUnion_le
    _ ≤ ∑ _ij : Fin (L + 1) × Fin (L + 1), (2 * (a + b) * R + 2) := by
      apply sum_le_sum
      intro ij _
      have hU := card_union_le (first N a b L R ij.1 ij.2) (second N a b L R ij.1 ij.2)
      have hfirst := first_card (R := R) hN ha hb ij.1 ij.2
      have hsecond := second_card (R := R) hN ha hb ij.1 ij.2
      nlinarith only [hU, hfirst, hsecond]
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]; ring

theorem mem_exceptional_of_parameter {N a b L R x y t : ℕ}
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (i j : Fin (L + 1))
    (hbaseX : startCompleteVertexLabel x L i = a * t) (hbaseY : startCompleteVertexLabel y L j = b * t)
    (hnear : |(a : ℤ) * t - N| ≤ R ∨ |(b : ℤ) * t - 2 * N| ≤ R) :
    (x, y) ∈ exceptional N a b L R := by
  have hu : b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j := by
    rw [hbaseX, hbaseY]
    ring
  have hsource : (x, y) ∈ sourcePairs N a b L i j := mem_sourcePairs.mpr ⟨hx, hy, hu⟩
  apply mem_biUnion.mpr
  refine ⟨(i, j), mem_univ _, ?_⟩
  rcases hnear with hnear | hnear
  · apply mem_union.mpr
    apply Or.inl
    apply mem_filter.mpr
    refine ⟨hsource, ?_⟩
    rw [hbaseX]
    simpa only [Nat.cast_mul] using hnear
  · apply mem_union.mpr
    apply Or.inr
    apply mem_filter.mpr
    refine ⟨hsource, ?_⟩
    rw [hbaseY]
    simpa only [Nat.cast_mul] using hnear

end PaperP1.DyadicEndpointPairs
