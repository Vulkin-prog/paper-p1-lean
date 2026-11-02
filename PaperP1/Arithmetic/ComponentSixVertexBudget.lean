module

public import PaperP1.Arithmetic.FullComponentMotifs
public import PaperP1.Combinatorics.DisjointSixVertexBudget

/-! # The exact surviving-vertex budget for the actual covered relation space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComponentSixVertexBudget

open Finset PaperP1.Arithmetic PaperP1.ThreeBlockCoordinates PaperP1.TripleCoverRank
  PaperP1.FullComponentMotifs PaperP1.CoverGraphResolution PaperP1.PinnedGraphResolution
  PaperP1.ThreeBlockComponents

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    DecidableEq (graph (rows X L H) D).ConnectedComponent := Classical.decEq _

def smallCount (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) : ℕ :=
  ((family X L H D).filter fun E ↦ E.card ≤ 5).card

theorem family_avoids (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    ∀ E ∈ family X L H D, Disjoint E D := by
  intro E hE
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hE
  have hfree := (mem_filter.mp hc).2.1
  apply disjoint_left.mpr
  intro v hv hvD
  exact hfree ⟨v, mem_union_left _ hvD, (mem_filter.mp hv).2⟩

theorem transverse_card {L : ℕ} {E : Finset (Vertex L)} (hE : TransverseMotifs.Transverse E) :
    3 ≤ E.card := by
  have h0 := (hE 0).card_pos
  have h1 := (hE 1).card_pos
  have h2 := (hE 2).card_pos
  have hcard := TransverseMotifs.card_decomposition E
  omega

theorem component_packing {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (D : Finset (Vertex L)) (hD : IsCover (rows X L H) D) :
    6 * fullCount X L H D + D.card ≤ 3 * (L + 1) + 3 * smallCount X L H D := by
  have hmin : ∀ E ∈ family X L H D, 3 ≤ E.card :=
    fun E hE ↦ transverse_card (family_data hX hH D hD E hE).1
  have hh := DisjointSixVertexBudget.six_vertex_budget univ D (family X L H D)
    (subset_univ D) (family_disjoint X L H D) (fun E _ ↦ subset_univ E) (family_avoids X L H D) hmin
  simpa only [family_card, card_univ, Fintype.card_prod, Fintype.card_fin, smallCount] using hh

theorem residual_budget {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L))
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)))
    (D : Finset (Vertex L)) (hD : IsCover (rows X L H) D) :
    6 * Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) + D.card ≤
      3 * (L + 1) + 3 * smallCount X L H D + 18 * (LocalDefectBound.primeCount H + 2) := by
  have hpack := component_packing hX hH D hD
  have hrank := (finite_rank_bound hX hH hinj hpair D hD).2
  omega

theorem residual_real_budget {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (hinj : ∀ i, Function.Injective (evenSquareClassMap (X i) L))
    (hpair : Pairwise (fun i j ↦ Disjoint (squareClassSpace (X i) L) (squareClassSpace (X j) L)))
    (D : Finset (Vertex L)) (hD : IsCover (rows X L H) D) :
    (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ) ≤
      (3 * (L + 1) - (D.card : ℝ)) / 6 + (smallCount X L H D : ℝ) / 2 +
        3 * ((LocalDefectBound.primeCount H : ℝ) + 2) := by
  have hh : 6 * (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ) + D.card ≤
      3 * (L + 1) + 3 * (smallCount X L H D : ℝ) + 18 * ((LocalDefectBound.primeCount H : ℝ) + 2) := by
    exact_mod_cast residual_budget hX hH hinj hpair D hD
  linarith only [hh]

end PaperP1.ComponentSixVertexBudget
