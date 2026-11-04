module

public import PaperP1.Arithmetic.PrefixSaturationCounts
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # The actual finite saturation graph and its maximum degree -/

/-! The centre range in this module is the positive prefix [2,N+2),
with exactly N centres; no critical lower bound on a centre is assumed. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixSaturationGraph

open Finset PaperP1.PrefixSaturationPrimes PaperP1.PrefixSaturationCounts PaperP1.PrimeProductBudget

abbrev Vertex (N : ℕ) := Ico 2 (N + 2)

def graph (B N : ℕ) (Y : ℝ) : SimpleGraph (Vertex N) where
  Adj x y := Edge B N Y x.val y.val ∨ Edge B N Y y.val x.val
  symm := ⟨fun _ _ h ↦ h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ h ↦ h.elim (fun h ↦ h.1 rfl) (fun h ↦ h.1 rfl)⟩

instance graphDecidable (B N : ℕ) (Y : ℝ) : DecidableRel (graph B N Y).Adj := Classical.decRel _

theorem neighbors_image (B N : ℕ) (Y : ℝ) (x : Vertex N) :
    ((graph B N Y).neighborFinset x).image Subtype.val = outgoing B N Y x.val ∪ incoming B N Y x.val := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    have hadj := ((graph B N Y).mem_neighborFinset x z).mp hz
    rcases hadj with h | h
    · exact mem_union_left _ ((mem_outgoing B N Y x.val z.val).mpr ⟨z.property, h⟩)
    · exact mem_union_right _ ((mem_incoming B N Y z.val x.val).mpr ⟨z.property, h⟩)
  · intro hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨hy, hedge⟩ := (mem_outgoing B N Y x.val y).mp hy
      let z : Vertex N := ⟨y, hy⟩
      exact mem_image.mpr ⟨z, ((graph B N Y).mem_neighborFinset x z).mpr (Or.inl hedge), rfl⟩
    · obtain ⟨hy, hedge⟩ := (mem_incoming B N Y y x.val).mp hy
      let z : Vertex N := ⟨y, hy⟩
      exact mem_image.mpr ⟨z, ((graph B N Y).mem_neighborFinset x z).mpr (Or.inr hedge), rfl⟩

theorem degree_eq_union (B N : ℕ) (Y : ℝ) (x : Vertex N) :
    (graph B N Y).degree x = (outgoing B N Y x.val ∪ incoming B N Y x.val).card := by
  rw [← neighbors_image]
  rw [card_image_of_injective _ Subtype.val_injective]
  exact (graph B N Y).card_neighborFinset_eq_degree x |>.symm

theorem directed_degrees_le_degree (B N : ℕ) (Y : ℝ) (x : Vertex N) :
    (outgoing B N Y x.val).card ≤ (graph B N Y).degree x ∧
      (incoming B N Y x.val).card ≤ (graph B N Y).degree x := by
  rw [degree_eq_union]
  exact ⟨card_le_card subset_union_left, card_le_card subset_union_right⟩

theorem degree_bound {B N : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y : ℝ) (hY : (B : ℝ) ≤ Y) (x : Vertex N) :
    ((graph B N Y).degree x : ℝ) ≤
      2 * (B : ℝ) ^ 2 * (2 * Real.exp 1 * (B : ℝ)) ^ assignmentExponent N Y := by
  have hout := outgoing_bound hN hB hBN x.property Y hY
  have hin := incoming_bound hN hB hBN x.property Y hY
  have hBpos : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : (B : ℝ) + 1 ≤ 2 * Real.exp 1 * (B : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hBpos]
  have hout' := hout.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hbase (assignmentExponent N Y)) (by positivity : (0 : ℝ) ≤ (B : ℝ) ^ 2))
  have hdegree : ((graph B N Y).degree x : ℝ) ≤
      (outgoing B N Y x.val).card + (incoming B N Y x.val).card := by
    rw [degree_eq_union]
    exact_mod_cast card_union_le (outgoing B N Y x.val) (incoming B N Y x.val)
  linarith

theorem maxDegree_bound {B N : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((graph B N Y).maxDegree : ℝ) ≤
      2 * (B : ℝ) ^ 2 * (2 * Real.exp 1 * (B : ℝ)) ^ assignmentExponent N Y := by
  have : Nonempty (Vertex N) := ⟨⟨N, mem_Ico.mpr ⟨by omega, by omega⟩⟩⟩
  obtain ⟨x, hx⟩ := (graph B N Y).exists_maximal_degree_vertex
  rw [hx]
  exact degree_bound hN hB hBN Y hY x

end PaperP1.PrefixSaturationGraph
