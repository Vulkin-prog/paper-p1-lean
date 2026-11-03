module

public import PaperP1.Arithmetic.MultiAnchorSaturationCounts
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # The actual t-anchor saturation graph and its maximum degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorGraph

open Finset PaperP1.MultiAnchorSaturation PaperP1.MultiAnchorSaturationCounts PaperP1.MultiAnchorPrimeBudget

abbrev Vertex (N : ℕ) := Ico N (2 * N)

def graph (t B N : ℕ) (Y : ℝ) : SimpleGraph (Vertex N) where
  Adj x y := Edge t B N Y x.val y.val ∨ Edge t B N Y y.val x.val
  symm := ⟨fun _ _ h ↦ h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ h ↦ h.elim (fun h ↦ h.1 rfl) (fun h ↦ h.1 rfl)⟩

instance graphDecidable (t B N : ℕ) (Y : ℝ) : DecidableRel (graph t B N Y).Adj := Classical.decRel _

theorem neighbors_image (t B N : ℕ) (Y : ℝ) (x : Vertex N) :
    ((graph t B N Y).neighborFinset x).image Subtype.val = outgoing t B N Y x.val ∪ incoming t B N Y x.val := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    have hadj := ((graph t B N Y).mem_neighborFinset x z).mp hz
    rcases hadj with h | h
    · exact mem_union_left _ ((mem_outgoing t B N Y x.val z.val).mpr ⟨z.property, h⟩)
    · exact mem_union_right _ ((mem_incoming t B N Y z.val x.val).mpr ⟨z.property, h⟩)
  · intro hy
    rcases mem_union.mp hy with hy | hy
    · obtain ⟨hy, hedge⟩ := (mem_outgoing t B N Y x.val y).mp hy
      let z : Vertex N := ⟨y, hy⟩
      exact mem_image.mpr ⟨z, ((graph t B N Y).mem_neighborFinset x z).mpr (Or.inl hedge), rfl⟩
    · obtain ⟨hy, hedge⟩ := (mem_incoming t B N Y y x.val).mp hy
      let z : Vertex N := ⟨y, hy⟩
      exact mem_image.mpr ⟨z, ((graph t B N Y).mem_neighborFinset x z).mpr (Or.inr hedge), rfl⟩

theorem degree_eq_union (t B N : ℕ) (Y : ℝ) (x : Vertex N) :
    (graph t B N Y).degree x = (outgoing t B N Y x.val ∪ incoming t B N Y x.val).card := by
  rw [← neighbors_image]
  rw [card_image_of_injective _ Subtype.val_injective]
  exact (graph t B N Y).card_neighborFinset_eq_degree x |>.symm

theorem directed_degrees_le_degree (t B N : ℕ) (Y : ℝ) (x : Vertex N) :
    (outgoing t B N Y x.val).card ≤ (graph t B N Y).degree x ∧
      (incoming t B N Y x.val).card ≤ (graph t B N Y).degree x := by
  rw [degree_eq_union]
  exact ⟨card_le_card subset_union_left, card_le_card subset_union_right⟩

theorem degree_bound {t B N : ℕ} (ht : 1 ≤ t) (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y : ℝ) (hY : (B : ℝ) ≤ Y) (x : Vertex N) :
    ((graph t B N Y).degree x : ℝ) ≤
      2 * (B : ℝ) ^ t * (2 * t * Real.exp 1 * (B : ℝ)) ^ assignmentExponent t N Y := by
  have hout := outgoing_bound (t := t) hN hB hBN x.property Y hY
  have hin := incoming_bound ht hN hB hBN x.property Y hY
  have hBpos : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
  have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hTone : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hfactor : 1 ≤ (t : ℝ) * Real.exp 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTone) (sub_nonneg.mpr hexp)]
  have hbase : (B : ℝ) + 1 ≤ 2 * t * Real.exp 1 * (B : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hBpos]
  have hout' := hout.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hbase (assignmentExponent t N Y)) (by positivity : (0 : ℝ) ≤ (B : ℝ) ^ t))
  have hdegree : ((graph t B N Y).degree x : ℝ) ≤
      (outgoing t B N Y x.val).card + (incoming t B N Y x.val).card := by
    rw [degree_eq_union]
    exact_mod_cast card_union_le (outgoing t B N Y x.val) (incoming t B N Y x.val)
  have hin' := hin.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity)
      (by nlinarith [Real.exp_pos 1] :
        (t : ℝ) * Real.exp 1 * B ≤ 2 * t * Real.exp 1 * B)
      (assignmentExponent t N Y)) (by positivity : (0 : ℝ) ≤ (B : ℝ) ^ t))
  linarith

theorem maxDegree_bound {t B N : ℕ} (ht : 1 ≤ t) (hN : 10 ≤ N) (hB : 2 ≤ B) (hBN : B ≤ N + 1)
    (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((graph t B N Y).maxDegree : ℝ) ≤
      2 * (B : ℝ) ^ t * (2 * t * Real.exp 1 * (B : ℝ)) ^ assignmentExponent t N Y := by
  have : Nonempty (Vertex N) := ⟨⟨N, mem_Ico.mpr ⟨le_rfl, by omega⟩⟩⟩
  obtain ⟨x, hx⟩ := (graph t B N Y).exists_maximal_degree_vertex
  rw [hx]
  exact degree_bound ht hN hB hBN Y hY x

end PaperP1.MultiAnchorGraph
