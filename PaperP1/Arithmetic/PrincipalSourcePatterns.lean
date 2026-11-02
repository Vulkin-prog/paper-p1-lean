module

public import PaperP1.Arithmetic.CompressedSourceBlocks
public import PaperP1.Model.PrincipalEdgeGeometry

/-! # Two channel choices and two vertex offsets parameterize every actual principal edge -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalSourcePatterns

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.DyadicEndpointPairs

abbrev Pattern (L : ℕ) := Fin 2 × (Fin (L + 1) × Fin (L + 1))

def a {L : ℕ} (p : Pattern L) : ℕ := ![2, 3] p.1
def b {L : ℕ} (p : Pattern L) : ℕ := ![3, 4] p.1

def sources (N L : ℕ) (p : Pattern L) : Finset (ℕ × ℕ) := sourcePairs N (a p) (b p) L p.2.1 p.2.2

def anchor {L : ℕ} (p : Pattern L) (xy : ℕ × ℕ) : ℕ := CompressedSourceBlocks.anchor (b p) L p.2.1 xy

def block (N L : ℕ) (p : Pattern L) (X : ℕ) : Finset ℕ :=
  CompressedSourceBlocks.block N (a p) (b p) L p.2.1 p.2.2 X

theorem properties {L : ℕ} (p : Pattern L) :
    0 < a p ∧ 0 < b p ∧ a p ≤ b p ∧ a p ≤ 4 ∧ b p ≤ 4 ∧ (a p).Coprime (b p) := by
  rcases p with ⟨k, ij⟩
  fin_cases k
  · change 0 < 2 ∧ 0 < 3 ∧ 2 ≤ 3 ∧ 2 ≤ 4 ∧ 3 ≤ 4 ∧ Nat.Coprime 2 3
    decide
  · change 0 < 3 ∧ 0 < 4 ∧ 3 ≤ 4 ∧ 3 ≤ 4 ∧ 4 ≤ 4 ∧ Nat.Coprime 3 4
    decide

theorem patterns_card (L : ℕ) : Fintype.card (Pattern L) = 2 * (L + 1) ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_fin, pow_two]

theorem anchor_injective {N L : ℕ} (hN : 0 < N) (p : Pattern L) :
    Set.InjOn (anchor p) (sources N L p : Set (ℕ × ℕ)) := by
  obtain ⟨ha, hb, _⟩ := properties p
  exact first_anchor_injective hN ha hb p.2.1 p.2.2

theorem space_eq {N L : ℕ} (hN : 2 ≤ N) (p : Pattern L) {xy : ℕ × ℕ} (hxy : xy ∈ sources N L p) :
    FiniteEvenSquareClasses.space (block N L p (anchor p xy)) = squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L := by
  obtain ⟨ha, hb, _⟩ := properties p
  exact CompressedSourceBlocks.space_eq hN ha hb p.2.1 p.2.2 hxy

theorem source_of_edge {N H L : ℕ} (hN : 0 < N) {e : Finset ℕ} (he : e ∈ PrincipalChannelEdges.edges N H L) :
    ∃ p : Pattern L, ∃ xy ∈ sources N L p, e = {xy.1, xy.2} := by
  obtain ⟨aa, bb, x, y, hab, heq, hx, hy, hunit, _hgeom⟩ := PrincipalEdgeGeometry.edge_data hN he
  obtain ⟨ij, hij⟩ := hunit
  have hcases : (aa = 2 ∧ bb = 3) ∨ (aa = 3 ∧ bb = 4) := by
    simpa only [PrincipalEdgeGeometry.channels, mem_insert, mem_singleton, Prod.mk.injEq] using hab
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨(0, ij), (x, y), ?_, heq⟩
    change (x, y) ∈ sourcePairs N 2 3 L ij.1 ij.2
    exact mem_sourcePairs.mpr ⟨hx, hy, NormalizedUnitCount.mem_units.mp hij⟩
  · refine ⟨(1, ij), (x, y), ?_, heq⟩
    change (x, y) ∈ sourcePairs N 3 4 L ij.1 ij.2
    exact mem_sourcePairs.mpr ⟨hx, hy, NormalizedUnitCount.mem_units.mp hij⟩

end PaperP1.PrincipalSourcePatterns
