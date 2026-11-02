module

public import PaperP1.Arithmetic.TripleCoverRank
public import PaperP1.Asymptotics.ManyPlanarSquareProducts

/-! # Every free three-block component is an actual disjoint transverse square-product motif -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FullComponentMotifs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.ThreeBlockCoordinates
  PaperP1.CoverGraphResolution PaperP1.ThreeBlockComponents PaperP1.TripleCoverRank
  PaperP1.PinnedGraphResolution PaperP1.SmoothMotifCodes

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    DecidableEq (graph (rows X L H) D).ConnectedComponent := Classical.decEq _

theorem component_nonempty (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L))
    (c : (graph (rows X L H) D).ConnectedComponent) :
    (componentVertices X L H D c).Nonempty := by
  obtain ⟨v, hv⟩ := c.nonempty_supp
  exact ⟨v, mem_filter.mpr ⟨mem_univ _, (c.mem_supp_iff v).mp hv⟩⟩

theorem vertices_injective (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    Function.Injective (componentVertices X L H D) := by
  intro c e hh
  obtain ⟨v, hv⟩ := component_nonempty X L H D c
  have he : v ∈ componentVertices X L H D e := by rwa [← hh]
  exact (mem_filter.mp hv).2.symm.trans (mem_filter.mp he).2

theorem components_disjoint (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    Pairwise (fun c e : (graph (rows X L H) D).ConnectedComponent ↦
      Disjoint (componentVertices X L H D c) (componentVertices X L H D e)) := by
  intro c e hce
  apply disjoint_left.mpr
  intro v hvc hve
  exact hce ((mem_filter.mp hvc).2.symm.trans (mem_filter.mp hve).2)

theorem component_transverse (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L))
    (c : (graph (rows X L H) D).ConnectedComponent) (hc : Full (graph (rows X L H) D) Prod.fst c) :
    TransverseMotifs.Transverse (componentVertices X L H D c) := by
  intro i
  obtain ⟨v, hv, hvi⟩ := hc i
  have hpair : (i, v.2) = v := Prod.ext hvi.symm rfl
  refine ⟨v.2, (TransverseMotifs.mem_offsets _ _ _).mpr ?_⟩
  rw [hpair]
  exact mem_filter.mpr ⟨mem_univ _, (c.mem_supp_iff v).mp hv⟩

theorem product_eq {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i)
    (D : Finset (Vertex L)) (c : (graph (rows X L H) D).ConnectedComponent) :
    naturalProduct X (componentVertices X L H D c) = componentProduct X L H D c := by
  unfold naturalProduct componentProduct
  apply prod_congr rfl
  intro v _
  rw [label, startCompleteVertexLabel_eq_offset (show 0 < X v.1 by have hh := hX v.1; omega)]
  rfl

def family (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) : Finset (Finset (Vertex L)) :=
  (fullComponents (graph (rows X L H) D) (pins (rows X L H) D) Prod.fst).image
    (componentVertices X L H D)

theorem family_card (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    (family X L H D).card = fullCount X L H D :=
  card_image_of_injective _ (vertices_injective X L H D)

theorem family_disjoint (X : Fin 3 → ℕ) (L H : ℕ) (D : Finset (Vertex L)) :
    (↑(family X L H D) : Set (Finset (Vertex L))).PairwiseDisjoint id := by
  intro E hE F hF hEF
  obtain ⟨c, _hc, rfl⟩ := mem_image.mp hE
  obtain ⟨e, _he, rfl⟩ := mem_image.mp hF
  have hce : c ≠ e := fun hh ↦ hEF (congrArg (componentVertices X L H D) hh)
  exact components_disjoint X L H D hce

theorem family_data {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (D : Finset (Vertex L)) (hD : IsCover (rows X L H) D) :
    ∀ E ∈ family X L H D, TransverseMotifs.Transverse E ∧ SquareOutside H X E := by
  intro E hE
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hE
  obtain ⟨hfree, hfull⟩ := (mem_filter.mp hc).2
  refine ⟨component_transverse X L H D c hfull, ?_⟩
  intro p hp
  have hp' : p ∈ DefectivePredicate.oddPrimeSupport (componentProduct X L H D c) := by
    simpa only [code, product_eq hX] using hp
  exact (DefectCounting.mem_smallPrimesUpTo.mp (component_product_supported hX hH hD c hfree hp')).2

theorem many_of_full_count {X : Fin 3 → ℕ} {L H : ℕ} (hX : ∀ i, 2 ≤ X i) (hH : L + 1 ≤ H)
    (D : Finset (Vertex L)) (hD : IsCover (rows X L H) D) (η : ℝ)
    (hcount : η * (L + 1) ≤ (fullCount X L H D : ℝ)) :
    ManyPlanarSquareProducts.Many η L H X :=
  ⟨family X L H D, family_disjoint X L H D, by rwa [family_card], family_data hX hH D hD⟩

end PaperP1.FullComponentMotifs
