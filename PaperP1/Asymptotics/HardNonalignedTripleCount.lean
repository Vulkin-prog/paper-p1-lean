module

public import PaperP1.Asymptotics.SharpTripleResidual
public import PaperP1.Asymptotics.StrongNoExactPairMass
public import PaperP1.Combinatorics.TwoEdgeTripleCover

/-! # The literal unresolved three-strong-pair population has subpower hosts

Two directed strong nonaligned pairs with one common endpoint recover
the triple. The internal subpower pair count therefore suffices. This
is a host count; an optimal bound for the joint weights remains separate.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HardNonalignedTripleCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SharpTripleResidual

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_count (C θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      ((hosts G L θ).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NP, _hNP, hp⟩ := StrongNoExactPairMass.uniform_count C θ (ε / 2) hθ (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨4 + NP + NG, by omega, ?_⟩
  intro N hN L hband G hG
  have hgeom := hg N (by omega) L hband
  have hL : 1 ≤ L := by omega
  have hwidth := hgeom.2.2.2.1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let P := ((dyadicBlock N) ×ˢ (dyadicBlock N)).filter fun p ↦
    ActualOffsetNonalignment.NoExact p.1 p.2 L ∧
      θ * L ≤ (FreeComponentRank.pairIntersectionRank p.1 p.2 L : ℝ)
  have hcount : (P.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    apply hp N (by omega) L hband P
    intro p hpP
    obtain ⟨hpD, hno, hrank⟩ := mem_filter.mp hpP
    exact ⟨(mem_product.mp hpD).1, (mem_product.mp hpD).2, hno, hrank⟩
  let f := fun pq : (ℕ × ℕ) × (ℕ × ℕ) ↦ ({pq.1.1, pq.1.2, pq.2.2} : Finset ℕ)
  have hsub : hosts G L θ ⊆ (P ×ˢ P).image f := by
    intro T hT
    obtain ⟨hTc, hHard⟩ := mem_filter.mp hT
    obtain ⟨hTp, _hconn⟩ := mem_filter.mp hTc
    obtain ⟨hTG, hcard⟩ := mem_powersetCard.mp hTp
    have hTN : T ⊆ dyadicBlock N := hTG.trans hG
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (show 1 < T.card by omega)
    have hpair : ({x, y} : Finset ℕ) ⊆ T := insert_subset_iff.mpr ⟨hx, singleton_subset_iff.mpr hy⟩
    obtain ⟨z, hz, hfresh, heq⟩ := TwoEdgeTripleCover.third_vertex hcard (card_pair hxy) hpair
    have hxz : x ≠ z := by
      intro hh
      apply hfresh
      rw [← hh]
      exact mem_insert_self _ _
    have hpoint (a : ℕ) (ha : a ∈ T) (b : ℕ) (hb : b ∈ T) (hab : a ≠ b) : (a, b) ∈ P := by
      have hd := hHard a ha b hb hab
      have hno := ActualOffsetNonalignment.of_nonaligned hL
        (by have hh := (mem_Ico.mp (hTN ha)).1; omega)
        (by have hh := (mem_Ico.mp (hTN hb)).1; omega) hd.1
      have hLB : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hTN ha, hTN hb⟩, hno,
        (mul_le_mul_of_nonneg_left hLB hθ.le).trans hd.2.le⟩
    apply mem_image.mpr
    refine ⟨((x, y), (x, z)), mem_product.mpr ⟨hpoint x hx y hy hxy, hpoint x hx z hz hxz⟩, ?_⟩
    dsimp [f]
    rw [heq]
    ext n
    simp only [mem_insert, mem_singleton, mem_union]
    tauto
  have hcard : (hosts G L θ).card ≤ P.card * P.card :=
    (card_le_card hsub).trans (card_image_le.trans (le_of_eq (card_product P P)))
  have hcardR : ((hosts G L θ).card : ℝ) ≤ (P.card : ℝ) * P.card := by exact_mod_cast hcard
  calc
    _ ≤ (P.card : ℝ) * P.card := hcardR
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul hcount hcount (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.HardNonalignedTripleCount
